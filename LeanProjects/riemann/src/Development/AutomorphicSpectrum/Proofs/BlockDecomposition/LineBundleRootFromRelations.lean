import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

abbrev wordSet {k : ℕ} {τ : Type} (w : Fin k → τ) : Multiset τ := Finset.univ.val.map w

theorem wordSet_update_add {k : ℕ} {τ : Type} (f : Fin k → τ) (l : Fin k) (a : τ) :
    wordSet (Function.update f l a) + {f l} = wordSet f + {a} := by
  have key : ∀ g : Fin k → τ, wordSet g = g l ::ₘ ((Finset.univ.erase l).val.map g) := by
    intro g
    rw [← Multiset.map_cons, Finset.erase_val, Multiset.cons_erase (Finset.mem_univ_val l)]
  have e : (Finset.univ.erase l).val.map (Function.update f l a) = (Finset.univ.erase l).val.map f :=
    Multiset.map_congr rfl fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase (show x ∈ Finset.univ.erase l from hx)) _ _
  rw [key, key f, Function.update_self, e, ← Multiset.singleton_add, ← Multiset.singleton_add (f l)]
  abel

theorem wordSet_update_rel {k : ℕ} {τ : Type} (f g : Fin k → τ) (l l' : Fin k) (a : τ) (h : f l = g l') :
    wordSet f + wordSet (Function.update g l' a) = wordSet (Function.update f l a) + wordSet g := by
  refine add_right_cancel (b := ({f l} : Multiset τ)) ?_
  have e₁ := wordSet_update_add f l a
  have e₂ := wordSet_update_add g l' a
  rw [← h] at e₂
  calc wordSet f + wordSet (Function.update g l' a) + {f l}
      = wordSet f + (wordSet (Function.update g l' a) + {f l}) := by abel
    _ = wordSet f + (wordSet g + {a}) := by rw [e₂]
    _ = (wordSet f + {a}) + wordSet g := by abel
    _ = (wordSet (Function.update f l a) + {f l}) + wordSet g := by rw [e₁]
    _ = _ := by abel

section Ring

variable {B τ : Type} [CommRing B] {k : ℕ} {x : (Fin k → τ) → B}

theorem mul_word_update
    (hrel : ∀ w₁ w₂ w₃ w₄ : Fin k → τ, wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄ →
      x w₁ * x w₂ = x w₃ * x w₄)
    {i j : τ} {l₀ : Fin k} {r : B} (hu : IsUnit (x fun _ => i))
    (hr : r * x (fun _ => i) = x (Function.update (fun _ => i) l₀ j))
    (w : Fin k → τ) (l : Fin k) (hw : w l = i) : r * x w = x (Function.update w l j) := by
  refine hu.mul_right_cancel ?_
  have := hrel _ _ _ _ (wordSet_update_rel w (fun _ => i) l l₀ j hw)
  rw [← hr] at this
  rw [← this]
  ring

theorem pow_mul_word_const
    (hrel : ∀ w₁ w₂ w₃ w₄ : Fin k → τ, wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄ →
      x w₁ * x w₂ = x w₃ * x w₄)
    {i j : τ} {l₀ : Fin k} {r : B} (hu : IsUnit (x fun _ => i))
    (hr : r * x (fun _ => i) = x (Function.update (fun _ => i) l₀ j)) :
    r ^ k * x (fun _ => i) = x fun _ => j := by
  have key : ∀ n, n ≤ k → r ^ n * x (fun _ => i) = x (fun l => if l.val < n then j else i) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hlt : n < k := hn
      have := mul_word_update hrel hu hr (fun l => if l.val < n then j else i) ⟨n, hlt⟩ (by simp)
      rw [pow_succ', mul_assoc, ih hlt.le, this]
      congr 1
      funext l
      by_cases h : l = ⟨n, hlt⟩
      · subst h; simp
      · have : l.val ≠ n := fun e => h (Fin.ext e)
        rw [Function.update_of_ne h]
        by_cases h' : l.val < n
        · simp [h', Nat.lt_succ_of_lt h']
        · have : ¬ l.val < n + 1 := by omega
          simp [h', this]
  rw [key k le_rfl]
  congr 1
  funext l
  simp

end Ring

theorem prod_update_mul {M τ : Type} [CommMonoid M] {k : ℕ} (φ : τ → M) (f : Fin k → τ) (l : Fin k) (a : τ) :
    (∏ m, φ (Function.update f l a m)) * φ (f l) = (∏ m, φ (f m)) * φ a := by
  have key : ∀ w : Fin k → τ, ∏ l, φ (w l) = ((wordSet w).map φ).prod := by
    intro w
    rw [Multiset.map_map]
    rfl
  have := congrArg (fun s => (s.map φ).prod) (wordSet_update_add f l a)
  simpa [Multiset.map_add, Multiset.prod_add, key] using this

section Root

variable {X : Scheme.{0}} {Q : LB X} {k : ℕ} (hk : 1 ≤ k) {τ : Type} (u : (Fin k → τ) → LB.Sec Q)

def oneLetter (i j : τ) : Fin k → τ := Function.update (fun _ => i) ⟨0, hk⟩ j

def VeroneseRel : Prop :=
  ∀ w₁ w₂ w₃ w₄ : Fin k → τ, wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄ →
    ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c

def rootChart (i : τ) : X.Opens := nonzeroLocus (u fun _ => i)

def rootRatio (i j : τ) : Γ(X, rootChart u i) := secRatio (u fun _ => i) (u (oneLetter hk i j))

variable {u}

theorem VeroneseRel.resG (h : VeroneseRel u) {W : X.Opens} {c : Q.ι} (hc : W ≤ Q.U c)
    (w₁ w₂ w₃ w₄ : Fin k → τ) (hw : wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₁).f c) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₂).f c) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₃).f c) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₄).f c) := by
  rw [← map_mul, ← map_mul, h _ _ _ _ hw c]

variable (u)

theorem rootRatio_chart {W : X.Opens} {i : τ} (j : τ) {c : Q.ι} (hi : W ≤ rootChart u i) (hc : W ≤ Q.U c) :
    resG X hi (rootRatio hk u i j) * resG X hc ((u fun _ => i).f c) =
      resG X hc ((u (oneLetter hk i j)).f c) :=
  (secRatio_on _ _ c hi hc).symm

theorem rootRatio_self (i : τ) : rootRatio hk u i i = 1 := by
  have : oneLetter hk i i = fun _ => i := Function.update_eq_self (⟨0, hk⟩ : Fin k) (fun _ : Fin k => i)
  rw [rootRatio, this]
  exact secRatio_self _

variable {u}

theorem rootRatio_mul (h : VeroneseRel u) {W : X.Opens} {i j : τ} (l : τ) (hi : W ≤ rootChart u i)
    (hj : W ≤ rootChart u j) :
    resG X hi (rootRatio hk u i j) * resG X hj (rootRatio hk u j l) = resG X hi (rootRatio hk u i l) := by
  refine ext_charts (u fun _ => i) hi fun c => ?_
  have hc : W ⊓ Q.U c ≤ Q.U c := inf_le_right
  have hi' : W ⊓ Q.U c ≤ rootChart u i := inf_le_left.trans hi
  have hj' : W ⊓ Q.U c ≤ rootChart u j := inf_le_left.trans hj
  have ui : IsUnit (resG X hc ((u fun _ => i).f c)) := isUnit_resG_sec _ c hi' hc
  have uj : IsUnit (resG X hc ((u fun _ => j).f c)) := isUnit_resG_sec _ c hj' hc
  refine ui.mul_right_cancel ?_
  rw [map_mul, resG_resG, resG_resG, resG_resG]
  have e3 := mul_word_update (x := fun w => resG X hc ((u w).f c)) (h.resG hc) (i := j) (j := l)
    (l₀ := ⟨0, hk⟩) uj (rootRatio_chart hk u l hj' hc) (oneLetter hk i j) ⟨0, hk⟩
    (by simp [oneLetter])
  have e4 : Function.update (oneLetter hk i j) ⟨0, hk⟩ l = oneLetter hk i l :=
    Function.update_idem _ _ _
  rw [e4] at e3
  rw [rootRatio_chart hk u l hi' hc, mul_right_comm, rootRatio_chart hk u j hi' hc, mul_comm]
  exact e3

theorem rootRatio_pow (h : VeroneseRel u) {W : X.Opens} {i : τ} (j : τ) {c : Q.ι}
    (hi : W ≤ rootChart u i) (hc : W ≤ Q.U c) :
    resG X hi (rootRatio hk u i j) ^ k * resG X hc ((u fun _ => i).f c) =
      resG X hc ((u fun _ => j).f c) :=
  pow_mul_word_const (x := fun w => resG X hc ((u w).f c)) (h.resG hc) (l₀ := ⟨0, hk⟩)
    (isUnit_resG_sec _ c hi hc) (rootRatio_chart hk u j hi hc)

def rootG (h : VeroneseRel u) (i j : τ) : Γ(X, rootChart u i ⊓ rootChart u j)ˣ where
  val := resG X inf_le_left (rootRatio hk u i j)
  inv := resG X inf_le_right (rootRatio hk u j i)
  val_inv := by
    rw [rootRatio_mul hk h i inf_le_left inf_le_right, rootRatio_self, map_one]
  inv_val := by
    rw [rootRatio_mul hk h j inf_le_right inf_le_left, rootRatio_self, map_one]

def rootLB (h : VeroneseRel u) : LB X := ⟨τ, rootChart u, rootG hk h⟩

theorem rootG_self (h : VeroneseRel u) (i : τ) :
    res (le_inf le_rfl le_rfl : rootChart u i ≤ rootChart u i ⊓ rootChart u i) (rootG hk h i i) = 1 :=
  Units.ext (by
    change resG X _ (resG X _ (rootRatio hk u i i)) = 1
    rw [rootRatio_self, map_one, map_one])

theorem rootG_cocycle (h : VeroneseRel u) (i j l : τ) :
    res (inf_le_left : rootChart u i ⊓ rootChart u j ⊓ rootChart u l ≤ rootChart u i ⊓ rootChart u j)
        (rootG hk h i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        rootChart u i ⊓ rootChart u j ⊓ rootChart u l ≤ rootChart u j ⊓ rootChart u l) (rootG hk h j l) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        rootChart u i ⊓ rootChart u j ⊓ rootChart u l ≤ rootChart u i ⊓ rootChart u l) (rootG hk h i l) :=
  Units.ext (by
    change resG X _ (resG X _ (rootRatio hk u i j)) * resG X _ (resG X _ (rootRatio hk u j l)) =
      resG X _ (resG X _ (rootRatio hk u i l))
    simp only [resG_resG]
    exact rootRatio_mul hk h l _ _)

theorem rootLB_isLB (h : VeroneseRel u) (hc : ⨆ i : τ, nonzeroLocus (u fun _ => i) = ⊤) :
    (rootLB hk h).IsLB where
  cover := hc
  g_self := rootG_self hk h
  cocycle := rootG_cocycle hk h

def rootIso (h : VeroneseRel u) : LB.Iso (pw (rootLB hk h) (k : ℤ)) Q where
  s p := (isUnit_resG_sec (u fun _ => (show τ from p.2)) p.1 inf_le_right inf_le_left).unit

theorem rootIso_isGen (h : VeroneseRel u) : (rootIso hk h).IsGen := by
  rintro ⟨c, i⟩ ⟨c', i'⟩
  let A := pw (rootLB hk h) (k : ℤ)
  have hp : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ Q.U c := inf_le_left.trans inf_le_left
  have hq : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ A.U i := inf_le_left.trans inf_le_right
  have hp' : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ Q.U c' := inf_le_right.trans inf_le_left
  have hq' : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ A.U i' := inf_le_right.trans inf_le_right
  have key : res (le_inf hp hq) (@id (Γ(X, Q.U c ⊓ A.U i)ˣ) ((rootIso hk h).s (c, i))) *
      res (le_inf hq hq') (A.g i i') = res (le_inf hp hp') (Q.g c c') *
        res (le_inf hp' hq') (@id (Γ(X, Q.U c' ⊓ A.U i')ˣ) ((rootIso hk h).s (c', i'))) := by
    refine Units.ext ?_
    have eg : resG X (le_inf hq hq') (A.g i i').val =
        resG X (show _ ≤ rootChart u (show τ from i) from hq) (rootRatio hk u i i') ^ k := by
      have : A.g i i' = (rootG hk h i i') ^ k := by
        change (rootG hk h i i') ^ (k : ℤ) = _
        exact zpow_natCast _ _
      rw [this, Units.val_pow_eq_pow_val]
      exact (map_pow (resG X (le_inf hq hq')) _ k).trans (congrArg (· ^ k) (resG_resG _ _ _))
    change resG X (le_inf hp hq) (resG X inf_le_left ((u fun _ => (show τ from i)).f c)) *
        resG X (le_inf hq hq') (A.g i i').val =
      resG X (le_inf hp hp') (Q.g c c').val *
        resG X (le_inf hp' hq') (resG X inf_le_left ((u fun _ => (show τ from i')).f c'))
    rw [resG_resG, resG_resG, ← sec_compat _ c c' hp hp', eg, mul_comm]
    exact rootRatio_pow hk h _ _ _
  change res (le_inf hp hq) (@id (Γ(X, Q.U c ⊓ A.U i)ˣ) ((rootIso hk h).s (c, i))) =
    res (le_inf hp hp') (Q.g c c') * (res (le_inf hq hq') (A.g i i'))⁻¹ *
      res (le_inf hp' hq') (@id (Γ(X, Q.U c' ⊓ A.U i')ˣ) ((rootIso hk h).s (c', i')))
  rw [mul_right_comm, ← key, mul_inv_cancel_right]

section Pull

variable {Y : Scheme.{0}} (b : Y ⟶ X) {L : LB Y} {d D : ℤ} (hD : d * k = D)
  (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D))

include hk in
theorem preimage_rootChart_le (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) (i : τ) :
    b ⁻¹ᵁ rootChart u i ≤ nonzeroLocus (a i) :=
  (nonzeroLocus_secPull _ _).ge.trans
    (((hm _).nonzeroLocus_eq (LB.isLB_pull hQ b) (isLB_pw hL D)).le.trans
      (nonzeroLocus_secMono_const hD a i hk).le)

theorem appLE_rootRatio_chart {W : Y.Opens} {i : τ} (j : τ) {c : Q.ι} (hi : W ≤ b ⁻¹ᵁ rootChart u i)
    (hc : W ≤ b ⁻¹ᵁ Q.U c) :
    (b.appLE _ W hi).hom (rootRatio hk u i j) * (b.appLE _ W hc).hom ((u fun _ => i).f c) =
      (b.appLE _ W hc).hom ((u (oneLetter hk i j)).f c) := by
  have hW : W ≤ b ⁻¹ᵁ (rootChart u i ⊓ Q.U c) := le_inf hi hc
  have e := congrArg (b.appLE (rootChart u i ⊓ Q.U c) W hW).hom
    (rootRatio_chart hk u j (inf_le_left : rootChart u i ⊓ Q.U c ≤ _) inf_le_right)
  rwa [map_mul, appLE_resG, appLE_resG, appLE_resG] at e

theorem appLE_rootRatio_mul (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) {W : Y.Opens} {i : τ} (j : τ)
    (hi : W ≤ b ⁻¹ᵁ rootChart u i) (p : L.ι) (hp : W ≤ L.U p) :
    (b.appLE _ W hi).hom (rootRatio hk u i j) * resG Y hp (chartFn (a i) p) =
      resG Y hp (chartFn (a j) p) := by
  have hnz : W ≤ nonzeroLocus (secPull (u fun _ => i) b) := hi.trans (nonzeroLocus_secPull _ _).ge
  refine ext_charts (secPull (u fun _ => i) b) hnz fun c' => ?_
  have hc' : W ⊓ (Q.pull b).U c' ≤ (Q.pull b).U c' := inf_le_right
  have hp' : W ⊓ (Q.pull b).U c' ≤ L.U p := inf_le_left.trans hp
  have hi' : W ⊓ (Q.pull b).U c' ≤ b ⁻¹ᵁ rootChart u i := inf_le_left.trans hi
  have hcb : W ⊓ (Q.pull b).U c' ≤ b ⁻¹ᵁ Q.U (c' ⟨⟩) := hc'.trans (pull_U Q b c').le
  let α : τ → Γ(Y, W ⊓ (Q.pull b).U c') := fun i => resG Y hp' (chartFn (a i) p)
  let β : (Fin k → τ) → Γ(Y, W ⊓ (Q.pull b).U c') :=
    fun w => (b.appLE (Q.U (c' ⟨⟩)) _ hcb).hom ((u w).f (c' ⟨⟩))
  let ρ : Γ(Y, W ⊓ (Q.pull b).U c') := (b.appLE _ _ hi').hom (rootRatio hk u i j)
  let t : Γ(Y, W ⊓ (Q.pull b).U c') := resG Y (le_inf hp' hc' : _ ≤ (pw L D).U p ⊓ (Q.pull b).U c')
    (@id (Γ(Y, (pw L D).U p ⊓ (Q.pull b).U c')ˣ) (θ.s (p, c'))).val
  have S : ∀ w, ∏ l, α (w l) = t * β w := fun w => by
    have e : resG Y (le_inf hp' hc' : _ ≤ (pw L D).U p ⊓ (Q.pull b).U c')
        (resG Y inf_le_left (∏ l, chartFn (a (w l)) p)) =
        resG Y (le_inf hp' hc' : _ ≤ (pw L D).U p ⊓ (Q.pull b).U c')
          ((@id (Γ(Y, (pw L D).U p ⊓ (Q.pull b).U c')ˣ) (θ.s (p, c'))).val *
            resG Y inf_le_right ((secPull (u w) b).f c')) :=
      congrArg _ (hm w (p, c'))
    rw [map_mul, resG_resG, resG_resG] at e
    refine (map_prod (resG Y hp') _ _).symm.trans (e.trans (congrArg (t * ·) ?_))
    exact (resG_resG _ _ _).trans rfl
  have hρ : ρ * β (fun _ => i) = β (oneLetter hk i j) := appLE_rootRatio_chart hk b j hi' hcb
  have e1 := prod_update_mul α (fun _ : Fin k => i) ⟨0, hk⟩ j
  have hP := S fun _ => i
  have uα : IsUnit (α i) := isUnit_resG_sec (a i) p
    (hi'.trans (preimage_rootChart_le hk b hD a θ hQ hL hm i)) hp'
  have uP : IsUnit (∏ _l : Fin k, α i) := by
    rw [Finset.prod_const]
    exact uα.pow _
  rw [map_mul, resG_appLE, resG_resG, resG_resG]
  change ρ * α i = α j
  refine uP.mul_left_cancel ?_
  calc (∏ _l : Fin k, α i) * (ρ * α i) = t * (ρ * β fun _ => i) * α i := by
        rw [hP]; ring
    _ = (∏ l, α (oneLetter hk i j l)) * α i := by rw [hρ, S]
    _ = _ := e1

def rootPullIso (h : VeroneseRel u) (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) :
    LB.Iso ((rootLB hk h).pull b) (pw L d) where
  s p := (isUnit_resG_sec (a (p.2 ⟨⟩)) p.1
    (inf_le_right.trans ((pull_U (rootLB hk h) b p.2).le.trans
      (preimage_rootChart_le hk b hD a θ hQ hL hm _))) inf_le_left).unit

theorem rootPullIso_isGen (h : VeroneseRel u) (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) :
    (rootPullIso hk b hD a θ h hQ hL hm).IsGen := by
  rintro ⟨l, i⟩ ⟨l', i'⟩
  let P := (rootLB hk h).pull b
  let M := pw L d
  have hp : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ M.U l := inf_le_left.trans inf_le_left
  have hq : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ P.U i := inf_le_left.trans inf_le_right
  have hp' : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ M.U l' := inf_le_right.trans inf_le_left
  have hq' : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ P.U i' := inf_le_right.trans inf_le_right
  have hi : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ b ⁻¹ᵁ rootChart u (i ⟨⟩) :=
    hq.trans (pull_U (rootLB hk h) b i).le
  have key : res (le_inf hp hq)
        (@id (Γ(Y, M.U l ⊓ P.U i)ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l, i))) *
      res (le_inf hq hq') (P.g i i') = res (le_inf hp hp') (M.g l l') *
        res (le_inf hp' hq')
          (@id (Γ(Y, M.U l' ⊓ P.U i')ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l', i'))) := by
    refine Units.ext ?_
    have eg : resG Y (le_inf hq hq') (P.g i i').val =
        (b.appLE _ _ hi).hom (rootRatio hk u (i ⟨⟩) (i' ⟨⟩)) := by
      have e := congrArg (fun v => resG Y (le_inf hq hq') (Units.val v)) (pull_g (rootLB hk h) b i i')
      refine e.trans ?_
      change resG Y _ (resG Y _ ((b.app _).hom (resG X inf_le_left (rootRatio hk u (i ⟨⟩) (i' ⟨⟩))))) = _
      refine (resG_resG _ _ _).trans ?_
      refine (congrArg (resG Y _) (app_resG b _ _)).trans ?_
      refine (resG_resG _ _ _).trans ?_
      rfl
    change resG Y (le_inf hp hq) (resG Y inf_le_left ((a (i ⟨⟩)).f l)) *
        resG Y (le_inf hq hq') (P.g i i').val =
      resG Y (le_inf hp hp') (M.g l l').val *
        resG Y (le_inf hp' hq') (resG Y inf_le_left ((a (i' ⟨⟩)).f l'))
    rw [resG_resG, resG_resG, ← sec_compat _ l l' hp hp', eg, mul_comm]
    exact appLE_rootRatio_mul hk b hD a θ hQ hL hm _ hi l hp
  change res (le_inf hp hq)
      (@id (Γ(Y, M.U l ⊓ P.U i)ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l, i))) =
    res (le_inf hp hp') (M.g l l') * (res (le_inf hq hq') (P.g i i'))⁻¹ *
      res (le_inf hp' hq')
        (@id (Γ(Y, M.U l' ⊓ P.U i')ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l', i')))
  rw [mul_right_comm, ← key, mul_inv_cancel_right]

end Pull

end Root

theorem exists_root_of_veronese : ∀ (X : Scheme.{0}) (Q : LB X), Q.IsLB → ∀ (k : ℕ), 1 ≤ k → ∀ (τ : Type) (u : (Fin k → τ) → LB.Sec Q), (∀ w₁ w₂ w₃ w₄ : Fin k → τ, (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c) → (⨆ i : τ, nonzeroLocus (u (fun _ => i)) = ⊤) → ∃ (A : LB X) (ω : LB.Iso (pw A (k : ℤ)) Q), A.IsLB ∧ ω.IsGen ∧ ∀ (Y : Scheme.{0}) (b : Y ⟶ X) (L : LB Y) (d D : ℤ) (hD : d * k = D) (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D)), L.IsLB → θ.IsGen → (∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) → LBIso (A.pull b) (pw L d) := by
  intro X Q hQ k hk τ u hrel hcov
  have h : VeroneseRel u := hrel
  exact ⟨rootLB hk h, rootIso hk h, rootLB_isLB hk h hcov, rootIso_isGen hk h,
    fun Y b L d D hD a θ hL _ hm => ⟨rootPullIso hk b hD a θ h hQ hL hm,
      rootPullIso_isGen hk b hD a θ h hQ hL hm⟩⟩

end GlobalTheory.CompanionTheory.FormalAlg
