import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.CupRep

open GlobalTheory.CompanionTheory.CocProd

section Filt
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

abbrev vl {k : ℕ} (f : CH.Cn (CH.modF A) k) (s : ComposableArrows C k) : A.obj (s.obj (Fin.last k)) := f s

def FC (a : IdF A) (k : ℕ) : AddSubgroup (CH.Cn (CH.modF A) k) where
  carrier := {f | ∀ s, vl f s ∈ a.S (s.obj (Fin.last k))}
  add_mem' := fun {f g} hf hg s => (a.S _).add_mem (hf s) (hg s)
  zero_mem' := fun s => (a.S _).zero_mem
  neg_mem' := fun {f} hf s => (a.S _).neg_mem (hf s)

theorem mem_FC {a : IdF A} {k : ℕ} {f : CH.Cn (CH.modF A) k} :
    f ∈ FC a k ↔ ∀ s, vl f s ∈ a.S (s.obj (Fin.last k)) := Iff.rfl

theorem term_mem {a : IdF A} {p n : ℕ} {f : CH.Cn (CH.modF A) p} (hf : f ∈ FC a p)
    (s : ComposableArrows C n) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    (show A.obj (s.obj (Fin.last n)) from CH.term (CH.modF A) s f g hg) ∈ a.S (s.obj (Fin.last n)) :=
  a.map_mem _ (mem_FC.1 hf (hg.functor ⋙ s))

theorem d_mem {a : IdF A} {k : ℕ} {f : CH.Cn (CH.modF A) k} (hf : f ∈ FC a k) :
    CH.d (CH.modF A) k f ∈ FC a (k + 1) := by
  refine mem_FC.2 fun s => ?_
  change (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • (show A.obj (s.obj (Fin.last (k + 1))) from
    (A.map (toLast i s)).hom (f (face i s)))) ∈ a.S _
  exact Ideal.sum_mem _ fun i _ => zsmul_mem (a.map_mem _ (mem_FC.1 hf (face i s))) _

def IsBd (Fil : ℤ → IdF A) : ∀ m : ℕ, CH.Cn (CH.modF A) m → Prop
  | 0, g => g = 0
  | n + 1, g => ∃ H : CH.Cn (CH.modF A) n, H ∈ FC (Fil ((n + 1 : ℕ) : ℤ)) n ∧ g = CH.d (CH.modF A) n H

theorem bil {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N]
    [Module R P] (μ : M →ₗ[R] N →ₗ[R] P) (L B g : M) (l b t : N) (B' x y : P) :
    μ L l - B' - (x + y) = μ (L - B - g) l + (μ g l - x) + (μ B b - B') + (μ B t - y) + μ B (l - (b + t)) := by
  simp only [map_sub, map_add, LinearMap.sub_apply]
  abel

end Filt

section Fr
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)

def fc {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) : CH.Cn (CH.modF Φ.A) j := fun s => E.form σ I x s

theorem cup_mem (hF : IsFil Φ Fil) {p q n : ℕ} (h : p + q = n) {r r' : ℕ} {f : CH.Cn (CH.modF Φ.A) p}
    {g : CH.Cn (CH.modF Φ.A) q} (hf : f ∈ FC (Fil r) p) (hg : g ∈ FC (Fil r') q) :
    (CH.mulP Φ.A).cupC h f g ∈ FC (Fil ((r + r' : ℕ) : ℤ)) n :=
  mem_FC.2 fun s => hF.mul r r' _ (term_mem hf s _ _) (term_mem hg s _ _)

theorem fc_mem (hF : IsFil Φ Fil) {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) :
    fc E σ I x ∈ FC (Fil (j : ℤ)) j := by
  refine mem_FC.2 fun s => ?_
  have hx : x ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
    rw [hF.top _ (by simp)]; trivial
  exact prod_mem hF _ (fun k => ga_mem E σ hF (I k) s k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).le)
      ((Fil _).map_mem (σ _) hx)

theorem d_fc_mem (hF : IsFil Φ Fil) (hc : E.GrConst Fil) {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) :
    CH.d (CH.modF Φ.A) j (fc E σ I x) ∈ FC (Fil ((j + 1 : ℕ) : ℤ)) (j + 1) := by
  refine mem_FC.2 fun s => ?_
  have hx : x ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
    rw [hF.top _ (by simp)]; trivial
  have h := d_form_mem E σ hF hc j 0 I x hx s
  have e : ((j : ℤ) + ((0 : ℕ) : ℤ)) + 1 = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e] at h
  exact h

theorem term_fc {j n : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C n)
    (g : Fin (j + 1) → Fin (n + 1)) (hg : Monotone g) :
    (show Φ.A.obj (s.obj (Fin.last n)) from CH.term (CH.modF Φ.A) s (fc E σ I x) g hg) =
      (∏ k : Fin j, ga E σ (I k) s (g k.castSucc) (g k.succ) (hg (Fin.castSucc_lt_succ (i := k)).le)) *
      (Φ.A.map (s.map (homOfLE (Fin.le_last (g (Fin.last j)))))).hom ((Φ.A.map (σ _)).hom x) := by
  change (Φ.A.map (s.map (homOfLE (Fin.le_last (g (Fin.last j)))))).hom (E.form σ I x (hg.functor ⋙ s)) = _
  unfold Frame.form
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have e : (hg.functor ⋙ s).map (homOfLE (Fin.le_last k.succ)) ≫ s.map (homOfLE (Fin.le_last (g (Fin.last j)))) =
      s.map (homOfLE (Fin.le_last (g k.succ))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  refine (map_map (Φ := Φ) ((hg.functor ⋙ s).map (homOfLE (Fin.le_last k.succ)))
    (s.map (homOfLE (Fin.le_last (g (Fin.last j))))) _).trans ?_
  unfold ga
  rw [e]
  rfl

theorem FC_anti (hF : IsFil Φ Fil) {r r' : ℤ} (h : r ≤ r') {k : ℕ} {f : CH.Cn (CH.modF Φ.A) k}
    (hf : f ∈ FC (Fil r') k) : f ∈ FC (Fil r) k :=
  mem_FC.2 fun s => hF.anti h _ (mem_FC.1 hf s)

theorem cup_fc (hF : IsFil Φ Fil) (hc : E.GrConst Fil) {j : ℕ} (I : Fin j → Fin d) (i : Fin d) (x y : Φ.A.obj E.D) :
    (CH.mulP Φ.A).cupC (rfl : j + 1 = j + 1) (fc E σ I x) (fc E σ ![i] y) -
      fc E σ (Fin.snoc (α := fun _ => Fin d) I i) (x * y) ∈ FC (Fil ((j + 1 + 1 : ℕ) : ℤ)) (j + 1) := by
  refine mem_FC.2 fun s => ?_
  set f : Fin (j + 1) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun k =>
    ga E σ (Fin.snoc (α := fun _ => Fin d) I i k) s k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).le with hf
  set X := (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x with hX
  set Y := (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom y with hY
  set W := (Φ.A.map (s.map (homOfLE (Fin.le_last (CH.front (rfl : j + 1 = j + 1) (Fin.last j)))))).hom
    ((Φ.A.map (σ _)).hom x) with hW
  have h1 : (show Φ.A.obj (s.obj (Fin.last (j + 1))) from CH.term (CH.modF Φ.A) s (fc E σ I x)
      (CH.front (rfl : j + 1 = j + 1)) (CH.front_mono _)) = (∏ k : Fin j, f k.castSucc) * W := by
    rw [term_fc]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hf, Fin.snoc_castSucc]
    exact ga_congr E σ _ s _ _ (by simp [CH.front]) (by simp [CH.front])
  have h2 : (show Φ.A.obj (s.obj (Fin.last (j + 1))) from CH.term (CH.modF Φ.A) s (fc E σ ![i] y)
      (CH.back (rfl : j + 1 = j + 1)) (CH.back_mono _)) = f (Fin.last j) * Y := by
    rw [term_fc, Fin.prod_univ_one]
    congr 1
    · simp only [hf, Fin.snoc_last]
      exact ga_congr E σ _ s _ _ (by simp [CH.back]) (by simp [CH.back])
    · refine (map_map (Φ := Φ) _ _ _).trans ?_
      rw [sec_last E σ s _ (by apply Fin.ext; simp [CH.back])]
  have h3 : vl (fc E σ (Fin.snoc (α := fun _ => Fin d) I i) (x * y)) s = (∏ k, f k) * (X * Y) := by
    change E.form σ _ _ s = _
    unfold Frame.form
    rw [map_mul]
    rfl
  have hx : x ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
    rw [hF.top _ (by simp)]; trivial
  have hWX : W - X ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    have h := hc 0 (σ _ ≫ s.map (homOfLE (Fin.le_last (CH.front (rfl : j + 1 = j + 1) (Fin.last j)))))
      (σ (s.obj (Fin.last (j + 1)))) hx
    rw [← map_map] at h
    simpa using h
  have key : vl ((CH.mulP Φ.A).cupC (rfl : j + 1 = j + 1) (fc E σ I x) (fc E σ ![i] y) -
      fc E σ (Fin.snoc (α := fun _ => Fin d) I i) (x * y)) s = (∏ k, f k) * ((W - X) * Y) := by
    change (show Φ.A.obj (s.obj (Fin.last (j + 1))) from CH.term (CH.modF Φ.A) s (fc E σ I x)
      (CH.front (rfl : j + 1 = j + 1)) (CH.front_mono _)) *
      (show Φ.A.obj (s.obj (Fin.last (j + 1))) from CH.term (CH.modF Φ.A) s (fc E σ ![i] y)
      (CH.back (rfl : j + 1 = j + 1)) (CH.back_mono _)) - vl (fc E σ (Fin.snoc (α := fun _ => Fin d) I i) (x * y)) s = _
    rw [h1, h2, h3, Fin.prod_univ_castSucc]
    ring
  rw [key]
  exact prod_mem hF f (fun k => ga_mem E σ hF _ s _ _ _) (q := 1) (Ideal.mul_mem_right _ _ hWX)

def h0 (h : ∀ T : C, Φ.A.obj T) : CH.Cn (CH.modF Φ.A) 0 := fun s => h (s.obj (Fin.last 0))

theorem cech_d_h0_eval (h : ∀ T : C, Φ.A.obj T) (u : ComposableArrows C 1) :
    vl (CH.d (CH.modF Φ.A) 0 (h0 h)) u = h (u.obj (Fin.last 1)) -
      (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h (u.obj 0)) := by
  have e0 : ∀ p : Fin 2, p = Fin.last 1 → (Φ.A.map (u.map (homOfLE (Fin.le_last p)))).hom (h (u.obj p)) =
      h (u.obj (Fin.last 1)) := by
    rintro p rfl
    have : (homOfLE (Fin.le_last (Fin.last 1)) : Fin.last 1 ⟶ Fin.last 1) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, u.map_id, Φ.A.map_id]
    rfl
  have e1 : ∀ p : Fin 2, p = 0 → (Φ.A.map (u.map (homOfLE (Fin.le_last p)))).hom (h (u.obj p)) =
      (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h (u.obj 0)) := by
    rintro p rfl
    rfl
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (show Φ.A.obj (u.obj (Fin.last 1)) from
    (Φ.A.map (u.map (homOfLE (Fin.le_last (i.succAbove (Fin.last 0)))))).hom (h (u.obj (i.succAbove (Fin.last 0))))) = _
  rw [Fin.sum_univ_two]
  change (-1 : ℤ) ^ 0 • (Φ.A.map (u.map (homOfLE (Fin.le_last ((0 : Fin 2).succAbove (Fin.last 0)))))).hom
      (h (u.obj ((0 : Fin 2).succAbove (Fin.last 0)))) + (-1 : ℤ) ^ 1 •
      (Φ.A.map (u.map (homOfLE (Fin.le_last ((1 : Fin 2).succAbove (Fin.last 0)))))).hom
      (h (u.obj ((1 : Fin 2).succAbove (Fin.last 0)))) = _
  rw [e0 _ (by decide), e1 _ (by decide)]
  simp [sub_eq_add_neg]

theorem bd_cup (hF : IsFil Φ Fil) (m : ℕ) (g : CH.Cn (CH.modF Φ.A) m) (hg : IsBd Fil m g)
    (l : CH.Cn (CH.modF Φ.A) 1) (hl : l ∈ FC (Fil ((1 : ℕ) : ℤ)) 1)
    (hdl : CH.d (CH.modF Φ.A) 1 l ∈ FC (Fil ((1 + 1 : ℕ) : ℤ)) (1 + 1)) :
    ∃ H : CH.Cn (CH.modF Φ.A) m, H ∈ FC (Fil ((m + 1 : ℕ) : ℤ)) m ∧
      (CH.mulP Φ.A).cupC (rfl : m + 1 = m + 1) g l - CH.d (CH.modF Φ.A) m H ∈ FC (Fil ((m + 1 + 1 : ℕ) : ℤ)) (m + 1) := by
  cases m with
  | zero =>
    have hg0 : g = 0 := hg
    subst hg0
    refine ⟨0, zero_mem _, ?_⟩
    simp
  | succ n =>
    obtain ⟨H, hH, rfl⟩ := hg
    refine ⟨(CH.mulP Φ.A).cupC (rfl : n + 1 = n + 1) H l, cup_mem hF rfl hH hl, ?_⟩
    rw [CrystallineSemistableComparison.P.leibniz]
    rw [sub_add_cancel_left]
    exact neg_mem (zsmul_mem (cup_mem hF (r := n + 1) (r' := 1 + 1) (by omega) hH hdl) _)

theorem b_cup_dh (hF : IsFil Φ Fil) (m : ℕ) (B : CH.Cn (CH.modF Φ.A) m) (hB : B ∈ FC (Fil (m : ℤ)) m)
    (hdB : CH.d (CH.modF Φ.A) m B ∈ FC (Fil ((m + 1 : ℕ) : ℤ)) (m + 1))
    (h : CH.Cn (CH.modF Φ.A) 0) (hh : h ∈ FC (Fil ((1 : ℕ) : ℤ)) 0) :
    ∃ H : CH.Cn (CH.modF Φ.A) m, H ∈ FC (Fil ((m + 1 : ℕ) : ℤ)) m ∧
      (CH.mulP Φ.A).cupC (rfl : m + 1 = m + 1) B (CH.d (CH.modF Φ.A) 0 h) - CH.d (CH.modF Φ.A) m H ∈
        FC (Fil ((m + 1 + 1 : ℕ) : ℤ)) (m + 1) := by
  refine ⟨(-1 : ℤ) ^ m • (CH.mulP Φ.A).cupC (add_zero m) B h, zsmul_mem (cup_mem hF _ hB hh) _, ?_⟩
  rw [map_zsmul, CrystallineSemistableComparison.P.leibniz, smul_add, smul_smul, ← mul_pow]
  have e : ((-1 : ℤ) * -1) ^ m = 1 := by simp
  rw [e, one_smul, sub_add_cancel_right]
  exact neg_mem (zsmul_mem (cup_mem hF (r := m + 1) (r' := 1) (by omega) hdB hh) _)

theorem sum_snoc {M : Type*} [AddCommMonoid M] (m : ℕ) (F : (Fin (m + 1) → Fin d) → M) :
    ∑ I, F I = ∑ I : Fin m → Fin d, ∑ i : Fin d, F (Fin.snoc (α := fun _ => Fin d) I i) := by
  let e : (Fin m → Fin d) × Fin d ≃ (Fin (m + 1) → Fin d) :=
    { toFun := fun p => Fin.snoc (α := fun _ => Fin d) p.1 p.2
      invFun := fun I => (Fin.init I, I (Fin.last m))
      left_inv := fun p => by simp
      right_inv := fun I => by simp }
  rw [← e.sum_comp, Fintype.sum_prod_type]
  rfl

theorem near (hF : IsFil Φ Fil) (hc : E.GrConst Fil) : ∀ (m : ℕ) (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1)
    (c : Fin m → Fin d → Φ.A.obj E.D) (h : Fin m → CH.Cn (CH.modF Φ.A) 0),
    (∀ k, h k ∈ FC (Fil ((1 : ℕ) : ℤ)) 0) →
    (∀ k, ℓ k - (∑ i, fc E σ ![i] (c k i) + CH.d (CH.modF Φ.A) 0 (h k)) ∈ FC (Fil ((1 + 1 : ℕ) : ℤ)) 1) →
    ∃ g, IsBd Fil m g ∧ cupListC Φ.A ℓ - ∑ I : Fin m → Fin d, fc E σ I (∏ k, c k (I k)) - g ∈
      FC (Fil ((m + 1 : ℕ) : ℤ)) m := by
  intro m
  induction m with
  | zero =>
    intro ℓ c h _ _
    refine ⟨0, rfl, ?_⟩
    have e : cupListC Φ.A ℓ - ∑ I : Fin 0 → Fin d, fc E σ I (∏ k, c k (I k)) - 0 = 0 := by
      funext s
      rw [sub_zero, Fintype.sum_unique, Pi.sub_apply]
      change (1 : Φ.A.obj (s.obj (Fin.last 0))) - E.form σ _ _ s = 0
      simp [Frame.form]
      exact sub_eq_zero.2 (map_one (Φ.A.map (σ (s.obj 0))).hom).symm
    rw [e]
    exact zero_mem _
  | succ m ih =>
    intro ℓ c h hh he
    obtain ⟨g, hg, hr⟩ := ih (fun i => ℓ i.castSucc) (fun i => c i.castSucc) (fun i => h i.castSucc)
      (fun k => hh _) (fun k => he _)
    set l := ℓ (Fin.last m) with hl_def
    set b : CH.Cn (CH.modF Φ.A) 1 := ∑ i, fc E σ ![i] (c (Fin.last m) i) with hb_def
    set t := CH.d (CH.modF Φ.A) 0 (h (Fin.last m)) with ht_def
    set B : CH.Cn (CH.modF Φ.A) m := ∑ I : Fin m → Fin d, fc E σ I (∏ k, c k.castSucc (I k)) with hB_def
    set L := cupListC Φ.A fun i => ℓ (Fin.castSucc i) with hL_def
    have hfe : l - (b + t) ∈ FC (Fil ((1 + 1 : ℕ) : ℤ)) 1 := he (Fin.last m)
    have ht : t ∈ FC (Fil ((1 : ℕ) : ℤ)) 1 := d_mem (hh _)
    have hb : b ∈ FC (Fil ((1 : ℕ) : ℤ)) 1 := sum_mem fun i _ => fc_mem E σ hF ![i] _
    have hl : l ∈ FC (Fil ((1 : ℕ) : ℤ)) 1 := by
      have := add_mem (FC_anti hF (r := ((1 : ℕ) : ℤ)) (by simp) hfe) (add_mem hb ht)
      rwa [sub_add_cancel] at this
    have hdb : CH.d (CH.modF Φ.A) 1 b ∈ FC (Fil ((1 + 1 : ℕ) : ℤ)) (1 + 1) := by
      rw [hb_def, map_sum]
      exact sum_mem fun i _ => d_fc_mem E σ hF hc ![i] _
    have hdl : CH.d (CH.modF Φ.A) 1 l ∈ FC (Fil ((1 + 1 : ℕ) : ℤ)) (1 + 1) := by
      have e : l = (l - (b + t)) + (b + t) := by abel
      rw [e, map_add, map_add, ht_def, CH.d_d, add_zero]
      exact add_mem (d_mem hfe) hdb
    have hB : B ∈ FC (Fil (m : ℤ)) m := sum_mem fun I _ => fc_mem E σ hF I _
    have hdB : CH.d (CH.modF Φ.A) m B ∈ FC (Fil ((m + 1 : ℕ) : ℤ)) (m + 1) := by
      rw [hB_def, map_sum]
      exact sum_mem fun I _ => d_fc_mem E σ hF hc I _
    obtain ⟨H₁, hH₁, hc₁⟩ := bd_cup hF m g hg l hl hdl
    obtain ⟨H₂, hH₂, hc₂⟩ := b_cup_dh hF m B hB hdB (h (Fin.last m)) (hh _)
    refine ⟨CH.d (CH.modF Φ.A) m (H₁ + H₂), ⟨H₁ + H₂, add_mem hH₁ hH₂, rfl⟩, ?_⟩
    have hcup : cupListC Φ.A ℓ = (CH.mulP Φ.A).cupC (rfl : m + 1 = m + 1) L l := rfl
    rw [hcup, map_add, bil _ L B g l b t]
    refine add_mem (add_mem (add_mem (add_mem ?_ hc₁) ?_) hc₂) ?_
    · exact cup_mem hF rfl hr hl
    · have e : (CH.mulP Φ.A).cupC (rfl : m + 1 = m + 1) B b -
          ∑ I : Fin (m + 1) → Fin d, fc E σ I (∏ k, c k (I k)) =
          ∑ I : Fin m → Fin d, ∑ i : Fin d, ((CH.mulP Φ.A).cupC (rfl : m + 1 = m + 1)
            (fc E σ I (∏ k, c k.castSucc (I k))) (fc E σ ![i] (c (Fin.last m) i)) -
            fc E σ (Fin.snoc (α := fun _ => Fin d) I i) ((∏ k, c k.castSucc (I k)) * c (Fin.last m) i)) := by
        have e1 : ∑ I : Fin (m + 1) → Fin d, fc E σ I (∏ k, c k (I k)) = ∑ I : Fin m → Fin d, ∑ i : Fin d,
            fc E σ (Fin.snoc (α := fun _ => Fin d) I i) ((∏ k, c k.castSucc (I k)) * c (Fin.last m) i) := by
          rw [sum_snoc]
          refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun i _ => ?_
          congr 1
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
        have e2 : (CH.mulP Φ.A).cupC (rfl : m + 1 = m + 1) B b = ∑ I : Fin m → Fin d, ∑ i : Fin d,
            (CH.mulP Φ.A).cupC (rfl : m + 1 = m + 1) (fc E σ I (∏ k, c k.castSucc (I k)))
              (fc E σ ![i] (c (Fin.last m) i)) := by
          rw [hB_def, LinearMap.map_sum₂]
          refine Finset.sum_congr rfl fun I _ => ?_
          rw [hb_def, map_sum]
        rw [e1, e2, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [← Finset.sum_sub_distrib]
      rw [e]
      exact sum_mem fun I _ => sum_mem fun i _ => cup_fc E σ hF hc I i _ _
    · exact cup_mem hF (r := m) (r' := 1 + 1) rfl hB hfe

theorem d_mul (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (w : Φ.A.obj E.D) {n : ℕ} {H : CH.Cn (CH.modF Φ.A) n}
    (hH : H ∈ FC (Fil ((n + 1 : ℕ) : ℤ)) n) (s : ComposableArrows C (n + 1)) :
    vl (CH.d (CH.modF Φ.A) n H) s * (Φ.A.map (σ _)).hom w -
      vl (CH.d (CH.modF Φ.A) n (fun u => (show Φ.A.obj (u.obj (Fin.last n)) from H u) * (Φ.A.map (σ _)).hom w)) s ∈
      (Fil ((n + 1 + 1 : ℕ) : ℤ)).S _ := by
  have hw : w ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
    rw [hF.top _ (by simp)]; trivial
  have e : vl (CH.d (CH.modF Φ.A) n H) s * (Φ.A.map (σ _)).hom w -
      vl (CH.d (CH.modF Φ.A) n (fun u => (show Φ.A.obj (u.obj (Fin.last n)) from H u) * (Φ.A.map (σ _)).hom w)) s =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((show Φ.A.obj (s.obj (Fin.last (n + 1))) from
        (Φ.A.map (toLast i s)).hom (H (face i s))) *
        ((Φ.A.map (σ _)).hom w - (Φ.A.map (σ _ ≫ toLast i s)).hom w)) := by
    change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (show Φ.A.obj (s.obj (Fin.last (n + 1))) from
        (Φ.A.map (toLast i s)).hom (H (face i s)))) * (Φ.A.map (σ _)).hom w -
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (show Φ.A.obj (s.obj (Fin.last (n + 1))) from
        (Φ.A.map (toLast i s)).hom ((show Φ.A.obj ((face i s).obj (Fin.last n)) from H (face i s)) *
          (Φ.A.map (σ _)).hom w))) = _
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_map, smul_mul_assoc, ← smul_sub, mul_sub]
  rw [e]
  refine Ideal.sum_mem _ fun i _ => zsmul_mem ?_ _
  have h1 : (show Φ.A.obj (s.obj (Fin.last (n + 1))) from (Φ.A.map (toLast i s)).hom (H (face i s))) ∈
      (Fil ((n + 1 : ℕ) : ℤ)).S _ := (Fil _).map_mem _ (mem_FC.1 hH (face i s))
  have h2 : (Φ.A.map (σ _)).hom w - (Φ.A.map (σ _ ≫ toLast i s)).hom w ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    have h := hc 0 (σ (s.obj (Fin.last (n + 1)))) (σ _ ≫ toLast i s) hw
    simpa using h
  exact hF.mul (n + 1) 1 _ h1 h2

theorem form_mul {j : ℕ} (I : Fin j → Fin d) (w x : Φ.A.obj E.D) (s : ComposableArrows C j) :
    E.form σ I (w * x) s = vl (fc E σ I x) s * (Φ.A.map (σ _)).hom w := by
  change E.form σ I (w * x) s = E.form σ I x s * _
  unfold Frame.form
  rw [map_mul]
  ring

end Fr

theorem cup_rep {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}  {d : ℕ}
    (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (m : ℕ) (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1) (c : Fin m → Fin d → Φ.A.obj E.D) (h : Fin m → ∀ T : C, Φ.A.obj T) :
    (∀ k T, h k T ∈ Φ.J.S T) →
    (∀ (k : Fin m) (u : ComposableArrows C 1), (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) -
      (∑ i, E.form σ ![i] (c k i) u + (h k (u.obj (Fin.last 1)) - (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) ∈ (Fil 2).S _) →
    ∀ (w : Φ.A.obj E.D) (r : ℤ), r = m → ∀ x : CH.H (gr Fil r) m,
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => (show Φ.A.obj (u.obj (Fin.last m)) from cupListC Φ.A ℓ u) * (Φ.A.map (σ _)).hom w) x →
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Fin m → Fin d, E.form σ I (w * ∏ k, c k (I k)) u) x := by
  intro hJ hl w r hr x hx
  subst hr
  have hh : ∀ k, h0 (h k) ∈ FC (Fil ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun s => by
    have := hJ k (s.obj (Fin.last 0))
    rw [← hF.one] at this
    rw [Nat.cast_one]
    exact this
  have he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (c k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k))) ∈
      FC (Fil ((1 + 1 : ℕ) : ℤ)) 1 := fun k => mem_FC.2 fun u => by
    have e : vl (ℓ k - (∑ i, fc E σ ![i] (c k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k)))) u =
        (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (c k i) u +
          (h k (u.obj (Fin.last 1)) - (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) := by
      rw [← cech_d_h0_eval]
      change _ - (vl (∑ i, fc E σ ![i] (c k i)) u + _) = _
      congr 2
      rw [vl, Finset.sum_apply]
      rfl
    rw [e]
    exact hl k u
  obtain ⟨g, hg, hn⟩ := near E σ hF hc m ℓ c (fun k => h0 (h k)) hh he
  have hz : ∀ u, (∑ I : Fin m → Fin d, E.form σ I (w * ∏ k, c k (I k)) u) =
      vl (∑ I : Fin m → Fin d, fc E σ I (∏ k, c k (I k))) u * (Φ.A.map (σ _)).hom w := by
    intro u
    rw [vl, Finset.sum_apply]
    change _ = (∑ I : Fin m → Fin d, vl (fc E σ I (∏ k, c k (I k))) u) * _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun I _ => form_mul E σ I w _ u
  cases m with
  | zero =>
    have hg0 : g = 0 := hg
    subst hg0
    refine rep_congr hx fun u => ?_
    rw [hz]
    have e := mem_FC.1 hn u
    have e' : vl (cupListC Φ.A ℓ - ∑ I : Fin 0 → Fin d, fc E σ I (∏ k, c k (I k)) - 0) u =
        vl (cupListC Φ.A ℓ) u - vl (∑ I : Fin 0 → Fin d, fc E σ I (∏ k, c k (I k))) u := by
      rw [sub_zero]; rfl
    rw [e'] at e
    rw [← sub_mul]
    have e2 : (((0 : ℕ) : ℤ) + 1) = ((0 + 1 : ℕ) : ℤ) := by simp
    rw [e2]
    exact Ideal.mul_mem_right _ _ e
  | succ n =>
    obtain ⟨H, hH, rfl⟩ := hg
    set Y : ∀ u : ComposableArrows C n, Φ.A.obj (u.obj (Fin.last n)) := fun u => (Φ.A.map (σ _)).hom w with hY
    let H' : CH.Cn (CH.modF Φ.A) n := fun u => (show Φ.A.obj (u.obj (Fin.last n)) from H u) * (Φ.A.map (σ _)).hom w
    have hH' : -H' ∈ FC (Fil ((n + 1 : ℕ) : ℤ)) n :=
      neg_mem (mem_FC.2 fun u => Ideal.mul_mem_right _ _ (mem_FC.1 hH u))
    have h1 := rep_add hx (rep_d (b := Fil (((n + 1 : ℕ) : ℤ) + 1)) (-H') (mem_FC.1 hH'))
    rw [add_zero] at h1
    refine rep_congr h1 fun u => ?_
    rw [hz]
    have e1 := mem_FC.1 hn u
    have e2 := d_mul E σ hF hc w hH u
    have e3 := (Fil _).S _ |>.add_mem (Ideal.mul_mem_right ((Φ.A.map (σ _)).hom w) _ e1) e2
    have e4 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [e4] at e3
    convert e3 using 1
    rw [map_neg]
    change _ + (-vl (CH.d (CH.modF Φ.A) n H') u) - _ = _
    change _ = (vl (cupListC Φ.A ℓ) u - vl (∑ I : Fin (n + 1) → Fin d, fc E σ I (∏ k, c k (I k))) u -
      vl (CH.d (CH.modF Φ.A) n H) u) * _ + (vl (CH.d (CH.modF Φ.A) n H) u * _ - vl (CH.d (CH.modF Φ.A) n H') u)
    ring

end GlobalTheory.CompanionTheory.CupRep
