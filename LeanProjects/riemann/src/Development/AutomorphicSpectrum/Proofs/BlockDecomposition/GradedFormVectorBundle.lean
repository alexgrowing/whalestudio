import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrVB
open GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem rp_class {W : X.Opens} {P : ObjectProperty (Thick (LL q))} {d r : ℕ} {u : Fin d → ∀ T : Thick (LL q), T.B}
    {x : Idx r d → Γ(X, W)} {c c' : HU (GF q r) P r} (h : Rp (W := W) P u x c) (h' : Rp (W := W) P u x c') : c = c' := by
  obtain ⟨f, hf, rfl, hs⟩ := h
  obtain ⟨f', hf', rfl, hs'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hs s).trans (hs' s).symm)
  subst e
  rfl

theorem inU_mono {W W' : X.Opens} (h : W' ≤ W) {T : Thick (LL q)} (hT : InU W' T) : InU W T :=
  hT.trans (fun _ hx => h hx)

theorem isLift_res {V W : X.Opens} (h : W ≤ V) {d : ℕ} {t : Fin d → Γ(X, V)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift V t u) {t' : Fin d → Γ(X, W)} (ht : ∀ i, t' i = rs h (t i)) : IsLift W t' u := by
  intro i T hT
  rw [ht, hu i T (inU_mono h hT), ev_res h T (inU_mono h hT) hT]

theorem st_iff {Q : ObjectProperty (Thick (LL q))} {W : X.Opens} (T : Thick (LL q)) :
    St Q {W} T ↔ Q T ∧ InU W T := by
  constructor
  · rintro ⟨h, V, hV, hi⟩
    obtain rfl : V = W := hV
    exact ⟨h, hi⟩
  · rintro ⟨h, hi⟩
    exact ⟨h, W, rfl, hi⟩

theorem inU_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (LL q)) :
    InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  have e : capO U i = ⨅ a ∈ (Finset.univ : Finset (Fin n)), U (i a) := by simp [capO]
  rw [e, GlobalTheory.T.inOpen_finite_inf_iff (fun a => U (i a)) Finset.univ T]
  simp

theorem capT_eq (l s : ℕ) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => SS q l s (U α)) i = SS q l s (capO U i) := by
  funext T
  refine propext ⟨fun h => ?_, fun h a => ?_⟩
  · exact (st_iff T).2 ⟨((st_iff T).1 (h 0)).1, (inU_capO U i T).2 fun a => ((st_iff T).1 (h a)).2⟩
  · obtain ⟨h1, h2⟩ := (st_iff T).1 h
    exact (st_iff T).2 ⟨h1, (inU_capO U i T).1 h2 a⟩

def Free (W : X.Opens) (P : ObjectProperty (Thick (LL q))) (r : ℕ) {d : ℕ} (u : Fin d → ∀ T : Thick (LL q), T.B) : Prop :=
  (∀ cl : HU (GF q r) P r, ∃ x, Rp (W := W) P u x cl) ∧ ∀ x : Idx r d → Γ(X, W), Rp (W := W) P u x 0 → x = 0

section Forms
variable {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
  {P : ObjectProperty (Thick (LL q))} {r : ℕ}

theorem rp_zero (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) :
    Rp (W := W) P u (0 : Idx r d → Γ(X, W)) (0 : HU (GF q r) P r) := by
  obtain ⟨c, hc⟩ := hE W t u hu P hP r 0
  have h2 := (hA W t u hu P hP r _ _ _ _ hc (hA W t u hu P hP r _ _ _ _ hc hc).2).1
  rw [add_neg_cancel, add_neg_cancel] at h2
  exact h2

theorem rp_sum (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) {κ' : Type} (S : Finset κ')
    (x : κ' → Idx r d → Γ(X, W)) (c : κ' → HU (GF q r) P r) (h : ∀ k ∈ S, Rp (W := W) P u (x k) (c k)) :
    Rp (W := W) P u (∑ k ∈ S, x k) (∑ k ∈ S, c k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact rp_zero hE hA hu hP
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hA W t u hu P hP r _ _ _ _ (h a (Finset.mem_insert_self a S))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).1

theorem rp_coef (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) (hF : Free W P r u)
    {x x' : Idx r d → Γ(X, W)} {c : HU (GF q r) P r} (h : Rp (W := W) P u x c) (h' : Rp (W := W) P u x' c) : x = x' := by
  have h2 := (hA W t u hu P hP r _ _ _ _ h (hA W t u hu P hP r _ _ _ _ h' h').2).1
  rw [add_neg_cancel c] at h2
  exact add_neg_eq_zero.1 (hF.2 _ h2)

theorem exists_equiv (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) (hF : Free W P r u) :
    ∃ e : HU (GF q r) P r ≃+ (Idx r d → Γ(X, W)), ∀ cl, Rp (W := W) P u (e cl) cl := by
  choose f hf using hF.1
  choose g hg using fun x => hE W t u hu P hP r x
  exact ⟨{ toFun := f, invFun := g, left_inv := fun c => rp_class (hg _) (hf c),
           right_inv := fun x => rp_coef hA hu hP hF (hf _) (hg x),
           map_add' := fun a b => rp_coef hA hu hP hF (hf _) (hA W t u hu P hP r _ _ _ _ (hf a) (hf b)).1 }, hf⟩

end Forms

theorem free_at (hL : StLoc) {l s : ℕ} (hb : TFBase (dividedPowersBot O) l s) {V W : X.Opens} (h : W ≤ V)
    (hW : IsAffineOpen W) {d : ℕ} (c : Coord q V d) {u : Fin d → ∀ T : Thick (LL q), T.B} (hu : IsLift V c.t u)
    {r : ℕ} (hr : r < s) {P : ObjectProperty (Thick (LL q))} (hP : P = SS q l s W) : Free W P r u := by
  subst hP
  obtain ⟨c', hc'⟩ := GlobalTheory.T.coordinates_restrict_affine_open c h hW
  exact hL l s hb q c' u (isLift_res h hu hc') r hr

theorem chg (hE : StExists) (hA : StAdd) (hR : StRes) (hAct : StAct) {W W₂ : X.Opens} (h : W ≤ W₂) {da db : ℕ}
    {ta : Fin da → Γ(X, W₂)} {tb : Fin db → Γ(X, W₂)} {ua : Fin da → ∀ T : Thick (LL q), T.B}
    {ub : Fin db → ∀ T : Thick (LL q), T.B} (hua : IsLift W₂ ta ua) (hub : IsLift W₂ tb ub)
    {P P₂ : ObjectProperty (Thick (LL q))} (hPP : P ≤ P₂) (hP : ∀ T, P T → InU W T) (hP₂ : ∀ T, P₂ T → InU W₂ T) {r : ℕ}
    (A : HU (GF q r) P₂ r ≃+ (Idx r da → Γ(X, W₂))) (hA' : ∀ cl, Rp (W := W₂) P₂ ua (A cl) cl)
    (B : HU (GF q r) P₂ r ≃+ (Idx r db → Γ(X, W₂))) (hB' : ∀ cl, Rp (W := W₂) P₂ ub (B cl) cl)
    [DecidableEq (Idx r db)] (x : HU (GF q r) P r) (y : Idx r db → Γ(X, W)) (hy : Rp (W := W) P ub y x) :
    Rp (W := W) P ua (fun k => ∑ k', rs h (A (B.symm (Pi.single k' 1)) k) * y k') x := by
  have hua' : IsLift W (fun i => rs h (ta i)) ua := isLift_res h hua fun _ => rfl
  have hub' : IsLift W (fun i => rs h (tb i)) ub := isLift_res h hub fun _ => rfl
  have hb1 : ∀ k', Rp (W := W₂) P₂ ub (Pi.single k' 1) (B.symm (Pi.single k' 1)) := fun k' => by
    have := hB' (B.symm (Pi.single k' 1))
    rwa [AddEquiv.apply_symm_apply] at this
  choose m hm using fun k' => hAct W P hP r (y k')
  have hd1 : ∀ k', Rp (W := W) P ub (fun I => y k' * rs h ((Pi.single k' 1 : Idx r db → Γ(X, W₂)) I))
      (m k' ((resU (GF q r) hPP).pull r (B.symm (Pi.single k' 1)))) := fun k' =>
    hm k' _ _ hub' _ _ (hR W₂ W h tb ub hub P₂ P hPP hP₂ hP r _ _ (hb1 k'))
  have hd2 : ∀ k', Rp (W := W) P ua (fun I => y k' * rs h (A (B.symm (Pi.single k' 1)) I))
      (m k' ((resU (GF q r) hPP).pull r (B.symm (Pi.single k' 1)))) := fun k' =>
    hm k' _ _ hua' _ _ (hR W₂ W h ta ua hua P₂ P hPP hP₂ hP r _ _ (hA' _))
  have s1 := rp_sum hE hA hub' hP Finset.univ _ _ fun k' _ => hd1 k'
  have s2 := rp_sum hE hA hua' hP Finset.univ _ _ fun k' _ => hd2 k'
  have e1 : (∑ k', fun I => y k' * rs h ((Pi.single k' 1 : Idx r db → Γ(X, W₂)) I)) = y := by
    funext I
    rw [Finset.sum_apply, Finset.sum_eq_single I]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne (Ne.symm hb)]
    · simp
  rw [e1] at s1
  rw [rp_class s1 hy] at s2
  convert s2 using 1
  funext k
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem capO_pair {ι : Type} (U : ι → X.Opens) (α β : ι) : capO U ![α, β] = U α ⊓ U β := by
  refine le_antisymm (le_inf (capO_le U _ 0) (capO_le U _ 1)) (le_iInf fun a => ?_)
  fin_cases a
  · exact inf_le_left
  · exact inf_le_right

theorem capT_inU (l s : ℕ) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (LL q))
    (h : capT (fun α => SS q l s (U α)) i T) : InU (capO U i) T :=
  (inU_capO U i T).2 fun a => ((st_iff T).1 (h a)).2

theorem ss_inU (l s : ℕ) (W : X.Opens) (T : Thick (LL q)) (h : SS q l s W T) : InU W T := ((st_iff T).1 h).2

section Main
variable {ι : Type} (U : ι → X.Opens) (d : ι → ℕ) (c : ∀ α, Coord q (U α) (d α))

def uu (α : ι) : Fin (d α) → ∀ T : Thick (LL q), T.B := fun k T => lft (U α) T ((c α).t k)

theorem uu_lift (α : ι) : IsLift (U α) (c α).t (uu U d c α) := fun k T h => lft_spec T h _

theorem uu_res (α : ι) {W : X.Opens} (h : W ≤ U α) : IsLift W (fun k => rs h ((c α).t k)) (uu U d c α) :=
  isLift_res h (uu_lift U d c α) fun _ => rfl

end Main

theorem main : StExists → StAdd → StSmul → StRes → StAct → StLoc → StVB := by
  classical
  intro hE hA hS hR hAct hL O _ l s hb X q ι _ U d c ha r hr
  have hPi : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (T : Thick (LL q)), capT (fun α => SS q l s (U α)) i T → InU (capO U i) T :=
    fun i T h => capT_inU l s U i T h
  have hFi : ∀ (n : ℕ) (a : Fin (n + 1)) (i : Fin (n + 1) → ι),
      Free (capO U i) (capT (fun α => SS q l s (U α)) i) r (uu U d c (i a)) := fun n a i =>
    free_at hL hb (capO_le U i a) (ha n i) (c (i a)) (uu_lift U d c (i a)) hr (capT_eq l s U i)
  choose E hEr using fun (n : ℕ) (a : Fin (n + 1)) (i : Fin (n + 1) → ι) =>
    exists_equiv hE hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i)
  have aff2 : ∀ α β, IsAffineOpen (U α ⊓ U β) := fun α β => by
    rw [← capO_pair]
    exact ha 1 _
  choose A hAr using fun α β => exists_equiv (P := SS q l s (U α ⊓ U β)) (r := r) hE hA (uu_res U d c α inf_le_left)
    (ss_inU l s (U α ⊓ U β)) (free_at hL hb inf_le_left (aff2 α β) (c α) (uu_lift U d c α) hr rfl)
  choose B hBr using fun α β => exists_equiv (P := SS q l s (U α ⊓ U β)) (r := r) hE hA (uu_res U d c β inf_le_right)
    (ss_inU l s (U α ⊓ U β)) (free_at hL hb inf_le_right (aff2 α β) (c β) (uu_lift U d c β) hr rfl)
  refine ⟨{ κ := fun α => Idx r (d α)
            fin := fun _ => inferInstance
            g := fun α β k k' => A α β ((B α β).symm (Pi.single k' 1)) k
            e := fun n a => AddEquiv.piCongrRight fun i => E n a i
            e_smul := ?_
            e_δ := ?_
            e_chg := ?_ }⟩
  · intro n a z x i k
    have := rp_coef hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i) (hEr n a i (z • x i))
      (hS _ _ _ (uu_res U d c (i a) (capO_le U i a)) _ (hPi i) r _ _ z (hEr n a i (x i)))
    exact congrFun this k
  · intro n a b x i k
    have := rp_coef hA (uu_res U d c (i (b.succAbove a)) (capO_le U i (b.succAbove a))) (hPi i) (hFi (n + 1) (b.succAbove a) i)
      (hEr (n + 1) (b.succAbove a) i _)
      (hR _ _ (capO_comp U i b.succAbove) _ _ (uu_res U d c (i (b.succAbove a)) (capO_le U (i ∘ b.succAbove) a))
        _ (capT (fun α => SS q l s (U α)) i) (fun _ h _ => h _) (hPi _) (hPi i) r _ _ (hEr n a (i ∘ b.succAbove) (x (i ∘ b.succAbove))))
    exact congrFun this k
  · intro n a b x i k
    have hle : capO U i ≤ U (i a) ⊓ U (i b) := le_inf (capO_le U i a) (capO_le U i b)
    have hPP : capT (fun α => SS q l s (U α)) i ≤ SS q l s (U (i a) ⊓ U (i b)) := fun T h =>
      (st_iff T).2 ⟨((st_iff T).1 (h a)).1, inU_mono hle (hPi i T h)⟩
    have := rp_coef hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i) (hEr n a i (x i))
      (chg hE hA hR hAct hle (uu_res U d c (i a) inf_le_left) (uu_res U d c (i b) inf_le_right) hPP (hPi i)
        (ss_inU l s _) (A (i a) (i b)) (hAr _ _) (B (i a) (i b)) (hBr _ _) (x i) _ (hEr n b i (x i)))
    exact congrFun this k

end GlobalTheory.CompanionTheory.GrVB
