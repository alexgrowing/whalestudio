import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterNormalizedEquivariantFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningMapIntoInducedLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningMapIntoInducedRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepresentationIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedSphericalVanishingAtIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement

noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology

namespace GlobalTheory.KSplit

section Local

open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a a' : ℕ} {ν α β : kˣ →* ℂˣ}

theorem mapA_add {z : ℂ} {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : IsEqv ν z l)
    {Φ Φ' : Matrix (Fin a) (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) (h' : Φ' ∈ SB _) :
    mapA a' l ν β (Φ + Φ') = mapA a' l ν β Φ + mapA a' l ν β Φ' := by
  funext x
  rw [Pi.add_apply, mapA, mapA, mapA, ← hl.1 _ (restrict_X0 (omA_mem_SB ν β 1 x h)) _ (restrict_X0 (omA_mem_SB ν β 1 x h'))]
  congr 1
  funext g
  simp only [omA, Pi.add_apply, mul_add]

theorem mapA_smul {z : ℂ} {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : IsEqv ν z l) (c : ℂ)
    {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapA a' l ν β (c • Φ) = c • mapA a' l ν β Φ := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, mapA, mapA, ← hl.2.1 c _ (restrict_X0 (omA_mem_SB ν β 1 x h))]
  congr 1
  funext g
  simp only [omA, Pi.smul_apply, smul_eq_mul]
  ring

theorem mapB_add {z : ℂ} {l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ} (hl : IsEqv ν z l)
    {Φ Φ' : Matrix (Fin a') (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) (h' : Φ' ∈ SB _) :
    mapB a l ν α (Φ + Φ') = mapB a l ν α Φ + mapB a l ν α Φ' := by
  funext x
  rw [Pi.add_apply, mapB, mapB, mapB, ← hl.1 _ (restrict_Y0 (omB_mem_SB ν α 1 x h)) _ (restrict_Y0 (omB_mem_SB ν α 1 x h'))]
  congr 1
  funext g
  simp only [omB, Pi.add_apply, mul_add]

theorem mapB_smul {z : ℂ} {l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ} (hl : IsEqv ν z l) (c : ℂ)
    {Φ : Matrix (Fin a') (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapB a l ν α (c • Φ) = c • mapB a l ν α Φ := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, mapB, mapB, ← hl.2.1 c _ (restrict_Y0 (omB_mem_SB ν α 1 x h))]
  congr 1
  funext g
  simp only [omB, Pi.smul_apply, smul_eq_mul]
  ring

theorem mapA_omA_left {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : IsEqv ν (((a + a' : ℕ) : ℂ) / 2) l) (g : GL (Fin a) k)
    {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapA a' l ν β (omA ν β g 1 Φ) = mapA a' l ν β Φ := by
  funext x
  have hs := restrict_X0 (omA_mem_SB ν β 1 x h)
  have e : omA ν β 1 x (omA ν β g 1 Φ) = omA ν β g 1 (omA ν β 1 x Φ) := by
    rw [← omA_mul, ← omA_mul, one_mul, mul_one, one_mul, mul_one]
  rw [mapA, mapA, e, ← hl.2.2 g⁻¹ 1 _ hs, ← hl.2.1 _ _ (comp_mul_mem_SB g⁻¹ 1 hs)]
  congr 1
  funext y
  simp only [omA, Pi.smul_apply, smul_eq_mul, map_one, map_inv, mul_one, Units.val_one, Matrix.mul_one, apow_one,
    Fintype.card_fin, apow_inv, Matrix.mul_assoc, neg_div, inv_one, Matrix.one_mul, one_mul]

theorem mapB_omB_left {l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ} (hl : IsEqv ν (((a + a' : ℕ) : ℂ) / 2) l) (g : GL (Fin a') k)
    {Φ : Matrix (Fin a') (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapB a l ν α (omB ν α g 1 Φ) = mapB a l ν α Φ := by
  funext x
  have hs := restrict_Y0 (omB_mem_SB ν α 1 x h)
  have e : omB ν α 1 x (omB ν α g 1 Φ) = omB ν α g 1 (omB ν α 1 x Φ) := by
    rw [← omB_mul, ← omB_mul, one_mul, mul_one, one_mul, mul_one]
  have hd : gdet (invT g)⁻¹ = gdet g := by rw [gdet, map_inv, ← gdet, gdet_invT, inv_inv]
  rw [mapB, mapB, e, ← hl.2.2 (invT g)⁻¹ 1 _ hs, ← hl.2.1 _ _ (comp_mul_mem_SB (invT g)⁻¹ 1 hs), hd]
  congr 1
  funext y
  simp only [omB, Pi.smul_apply, smul_eq_mul, map_one, mul_one, Units.val_one, Matrix.mul_one, apow_one,
    Fintype.card_fin, Matrix.mul_assoc, invT_inv_val, transpose_one, Matrix.one_mul, one_mul]

theorem mapA_ne_zero {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : ∃ φ ∈ SB _, l φ ≠ 0) :
    ∃ Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k), mapA a' l ν β Φ 1 ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := hl
  have hf := frame_rel (k := k) (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))
  obtain ⟨Φ, hΦ, h⟩ := exists_extend_SB hf.1 hf.2.2.1 hf.2.2.2.2 hφ
  refine ⟨Φ, hΦ, ?_⟩
  have e : omA ν β 1 1 Φ = Φ := by funext X; simp [omA]
  rw [mapA, e, funext h]
  exact h0

theorem mapB_ne_zero {l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ} (hl : ∃ φ ∈ SB _, l φ ≠ 0) :
    ∃ Φ ∈ SB (Matrix (Fin a') (Fin (a + a')) k), mapB a l ν α Φ 1 ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := hl
  have hf := frame_rel (k := k) (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))
  obtain ⟨Φ, hΦ, h⟩ := exists_extend_SB hf.2.1 hf.2.2.2.1 ((add_comm _ _).trans hf.2.2.2.2) hφ
  refine ⟨Φ, hΦ, ?_⟩
  have e : omB ν α 1 1 Φ = Φ := by funext X; simp [omB]
  rw [mapB, e, funext h]
  exact h0

theorem indicator_congr {m n m' n' : Type} {X : Matrix m n k} {Y : Matrix m' n' k} (h : X ∈ intM k m n ↔ Y ∈ intM k m' n') :
    (intM k m n).indicator (1 : Matrix m n k → ℂ) X = (intM k m' n').indicator (1 : Matrix m' n' k → ℂ) Y := by
  by_cases hX : X ∈ intM k m n
  · rw [Set.indicator_of_mem hX, Set.indicator_of_mem (h.1 hX)]; rfl
  · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (mt h.2 hX)]

theorem mul_mem_intM_iff {m : Type} [Fintype m] [DecidableEq m] {n : ℕ} {u : GL (Fin n) k} (hu : u ∈ KO k (Fin n))
    (X : Matrix m (Fin n) k) : X * u.val ∈ intM k m (Fin n) ↔ X ∈ intM k m (Fin n) := by
  have := mul_mul_mem_matLat_iff (one_mem (KO k m)) hu X
  rwa [Units.val_one, Matrix.one_mul, mem_matLat_stdLat, mem_matLat_stdLat] at this

theorem mul_frame_mem_intM {R D : Type} [Fintype R] [DecidableEq R] [Fintype D] {P : Matrix R D k} (hP : P * Pᵀ = 1)
    (hi : P ∈ intM k R D) (g : Matrix R R k) : g * P ∈ intM k R D ↔ g ∈ intM k R R := by
  refine ⟨fun h => ?_, fun h i j => Subring.sum_mem _ fun l _ => mul_mem (h i l) (hi l j)⟩
  rw [← Matrix.mul_one g, ← hP, ← Matrix.mul_assoc]
  exact fun i j => Subring.sum_mem _ fun l _ => mul_mem (h i l) (hi j l)

theorem mapA_unit (hβ : IsUnram β) (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) :
    (∀ u ∈ KO k (Fin (a + a')), ∀ h, mapA a' l ν β ((intM k _ _).indicator 1) (h * u) =
      mapA a' l ν β ((intM k _ _).indicator 1) h) ∧
    mapA a' l ν β ((intM k _ _).indicator 1) 1 = l ((intM k _ _).indicator 1) := by
  refine ⟨fun u hu h => ?_, ?_⟩
  · rw [← mapA_omA_right]
    congr 1
    funext X
    have hv := valuation_gdet_of_mem_KO hu
    simp only [omA, map_one, inv_one, Units.val_one, apow_one, hβ _ hv, apow_of_valuation_eq_one hv, one_mul, Matrix.one_mul]
    exact indicator_congr (mul_mem_intM_iff (invT_mem_KO hu) X)
  · have e : omA ν β 1 1 ((intM k (Fin a) (Fin (a + a'))).indicator 1) = (intM k _ _).indicator 1 := by funext X; simp [omA]
    rw [mapA, e]
    congr 1
    funext g
    refine indicator_congr (mul_frame_mem_intM (frame_rel _).1 (fun i j => ?_) g)
    simp only [X0, of_apply]; split_ifs <;> simp

theorem mapB_unit (hα : IsUnram α) (l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ) :
    (∀ u ∈ KO k (Fin (a + a')), ∀ h, mapB a l ν α ((intM k _ _).indicator 1) (h * u) =
      mapB a l ν α ((intM k _ _).indicator 1) h) ∧
    mapB a l ν α ((intM k _ _).indicator 1) 1 = l ((intM k _ _).indicator 1) := by
  refine ⟨fun u hu h => ?_, ?_⟩
  · rw [← mapB_omB_right]
    congr 1
    funext X
    have hv := valuation_gdet_of_mem_KO hu
    simp only [omB, map_one, Units.val_one, apow_one, hα _ hv, apow_of_valuation_eq_one hv, one_mul, transpose_one,
      Matrix.one_mul]
    exact indicator_congr (mul_mem_intM_iff hu X)
  · have e : omB ν α 1 1 ((intM k (Fin a') (Fin (a + a'))).indicator 1) = (intM k _ _).indicator 1 := by funext X; simp [omB]
    rw [mapB, e]
    congr 1
    funext g
    refine indicator_congr (mul_frame_mem_intM (frame_rel _).2.1 (fun i j => ?_) g)
    simp only [Y0, of_apply]; split_ifs <;> simp

theorem IsSmU.div (hα : IsSmU α) (hβ : IsSmU β) : IsSmU (α / β) := by
  refine ⟨Subgroup.isOpen_mono (H₁ := α.ker ⊓ β.ker) (fun x hx => ?_) (hα.1.inter hβ.1), fun x => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.div_apply, hx.1, hx.2, div_one]
  · rw [MonoidHom.div_apply, Units.val_div_eq_div_val, norm_div, hα.2, hβ.2, div_one]

end Local

theorem exists_linear_ext {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ U)
    (I : Submodule ℂ V) (f : U → V) (hI : ∀ x ∈ S, f x ∈ I) (hadd : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x + f y)
    (hsm : ∀ c : ℂ, ∀ x ∈ S, f (c • x) = c • f x) : ∃ p : U →ₗ[ℂ] I, ∀ x ∈ S, (p x : V) = f x := by
  let q : S →ₗ[ℂ] I :=
    { toFun := fun x => ⟨f x, hI x x.2⟩
      map_add' := fun x y => Subtype.ext (hadd x x.2 y y.2)
      map_smul' := fun c x => Subtype.ext (hsm c x x.2) }
  obtain ⟨p, hp⟩ := LinearMap.exists_extend q
  exact ⟨p, fun x hx => congrArg Subtype.val (LinearMap.congr_fun hp ⟨x, hx⟩)⟩

theorem map_eq_top {U H : Type} [AddCommGroup U] [Module ℂ U] [Group H] (S : Submodule ℂ U) (I : Submodule ℂ (H → ℂ))
    (hI : ∀ N : Submodule ℂ (H → ℂ), N ≤ I → (∀ f ∈ N, ∀ x, (fun h => f (h * x)) ∈ N) → N = ⊥ ∨ N = I)
    (p : U →ₗ[ℂ] I) (heq : ∀ φ ∈ S, ∀ x, ∃ φ₁ ∈ S, (p φ₁ : H → ℂ) = fun h => (p φ : H → ℂ) (h * x))
    (hne : ∃ φ ∈ S, p φ ≠ 0) : S.map p = ⊤ := by
  rcases hI ((S.map p).map I.subtype) (Submodule.map_subtype_le _ _) (by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩ x
    obtain ⟨φ₁, h1, h2⟩ := heq φ hφ x
    exact ⟨_, ⟨φ₁, h1, rfl⟩, h2⟩) with h | h
  · obtain ⟨φ, hφ, h0⟩ := hne
    have : (p φ : H → ℂ) ∈ (S.map p).map I.subtype := ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact absurd (Subtype.ext this) h0
  · exact Submodule.map_injective_of_injective I.injective_subtype (h.trans (Submodule.map_subtype_top I).symm)

section Adelic

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KFinLoc
open GlobalTheory.SplitFlip (omA omB)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ₁ x / χ₂ x
    exact h₁.1.div' h₂.1
  · rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E}
    {m m' : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' m') : ResEtaPow K (χ / χ') (m + m') := by
  intro u
  rw [MonoidHom.div_apply, Circle.coe_div, h u, h' u]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

variable {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_big (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div h.chars.resβ h.chars.resα, h.weil⟩

theorem isPair_small (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    add_comm a' a ▸ resEtaPow_div h.chars.resα h.chars.resβ, h.weil'⟩

theorem chrW_div (χ χ' : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) : chrW (χ / χ') t = chrW χ t / chrW χ' t := by
  ext x
  simp [chrW, locChar]

omit [NumberField E] in

theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) (v : Pl F) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

theorem core (hP : GlobalTheory.FunPr.Hypotheses₂) (hT : IsTriple B G X om om') {v : Pl F} (t : E →ₐ[F] Fv F v)
    {b : GL (Fin a) (Fv F v)} {b' : GL (Fin a') (Fv F v)} {c : GL (Fin (a + a')) (Fv F v)} {ι ι'}
    (hι : G.M.IsLinW B.ψ t b c ι) (hι' : G.M'.IsLinBar B.ψ t b' c ι') {l l'}
    (hl : IsEqv (chrW X.α t / chrW X.β t) (((a + a' : ℕ) : ℂ) / 2) l) (hl0 : ∃ φ ∈ GlobalTheory.SplitWeil.SB _, l φ ≠ 0)
    (hl' : IsEqv (chrW X.α t / chrW X.β t) (((a + a' : ℕ) : ℂ) / 2) l') (hl0' : ∃ φ ∈ GlobalTheory.SplitWeil.SB _, l' φ ≠ 0) :
    ∃ R : FinMaps F a a', ∃ j : R.Pi v → GL (Fin (a + a')) (Fv F v) → ℂ, Function.Injective j ∧ j 0 = 0 ∧
      (∀ φ ∈ SB _, j (R.p v φ) = mapA a' l (chrW X.α t / chrW X.β t) (chrW X.β t) (ι φ)) ∧
      (∀ φ ∈ SB _, j (R.p' v φ) = mapB a l' (chrW X.α t / chrW X.β t) (chrW X.α t) (ι' φ)) ∧
      ((v ∉ X.T → R.p v (G.M.vac v) = R.p' v (G.M'.vac v) ∧ R.p v (G.M.vac v) ≠ 0) →
        (∀ hv : v ∈ B.P, v ∈ X.T → IsZetaAt B G X R ⟨v, hv⟩) → FinMapsAt B G X om om' R v) := by
  classical
  have hα := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hT.chars.heckeα v t).1
  have hβ := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hT.chars.heckeβ v t).1
  set α := chrW X.α t with hαd
  set β := chrW X.β t with hβd
  have hb := Model.IsLin.bij hι
  have hb' := Model.IsLin.bij hι'
  have m : ∀ φ ∈ SB _, ι φ ∈ GlobalTheory.SplitWeil.SB _ := fun φ h => hb.mapsTo h
  have m' : ∀ φ ∈ SB _, ι' φ ∈ GlobalTheory.SplitWeil.SB _ := fun φ h => hb'.mapsTo h
  have hI := GlobalTheory.T.induced_representation_irreducible hP.bernsteinUnitaryProductIrreducible (Fv F v) a a' α β hα hβ
  obtain ⟨p, hp⟩ := exists_linear_ext (SB _) (indSp a a' α β) (fun φ => mapA a' l (α / β) β (ι φ))
    (fun φ h => GlobalTheory.T.intertwining_map_into_induced_left _ a a' α β l hβ hl _ (m φ h))
    (fun φ h φ' h' => by simp only [map_add]; exact mapA_add hl (m φ h) (m φ' h'))
    (fun z φ h => by simp only [map_smul]; exact mapA_smul hl z (m φ h))
  obtain ⟨p', hp'⟩ := exists_linear_ext (SB _) (indSp a a' α β) (fun φ => mapB a l' (α / β) α (ι' φ))
    (fun φ h => GlobalTheory.T.intertwining_map_into_induced_right _ a a' α β l' hα hl' _ (m' φ h))
    (fun φ h φ' h' => by simp only [map_add]; exact mapB_add hl' (m' φ h) (m' φ' h'))
    (fun z φ h => by simp only [map_smul]; exact mapB_smul hl' z (m' φ h))
  have act := fun g hg h hh φ hφ φ₁ hφ₁ H => GlobalTheory.T.linear_witt_model_unitary_action hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_big hT) v t b c ι hι
    g hg h hh φ hφ φ₁ hφ₁ H
  have act' := fun g hg h hh φ hφ φ₁ hφ₁ H => GlobalTheory.T.linear_bar_model_unitary_action hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (isPair_small hT) v t b' c ι' hι'
    g hg h hh φ hφ φ₁ hφ₁ H
  rw [chrW_div, inv_div, ← hαd, ← hβd] at act
  rw [chrW_div, ← hαd, ← hβd] at act'
  have tr : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ →
      (p φ₁ : _ → ℂ) = fun y => (p φ : _ → ℂ) (y * locMat t c h) := fun h hh φ hφ φ₁ hφ₁ H => by
    funext y
    rw [hp _ hφ₁, hp _ hφ, act 1 (one_mem_UAt _ v) h hh φ hφ φ₁ hφ₁ H, map_one, mapA_omA_right]
  have tr' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ →
      (p' φ₁ : _ → ℂ) = fun y => (p' φ : _ → ℂ) (y * locMat t c h) := fun h hh φ hφ φ₁ hφ₁ H => by
    funext y
    rw [hp' _ hφ₁, hp' _ hφ, act' 1 (one_mem_UAt _ v) h hh φ hφ φ₁ hφ₁ H, map_one, mapB_omB_right]
  have ne : ∃ φ ∈ SB _, p φ ≠ 0 := by
    obtain ⟨Φ, hΦ, h0⟩ := mapA_ne_zero (a' := a') (ν := α / β) (β := β) hl0
    obtain ⟨φ, hφ, rfl⟩ := hb.surjOn hΦ
    exact ⟨φ, hφ, fun h => h0 (by rw [← hp φ hφ, h]; rfl)⟩
  have ne' : ∃ φ ∈ SB _, p' φ ≠ 0 := by
    obtain ⟨Φ, hΦ, h0⟩ := mapB_ne_zero (a := a) (ν := α / β) (α := α) hl0'
    obtain ⟨φ, hφ, rfl⟩ := hb'.surjOn hΦ
    exact ⟨φ, hφ, fun h => h0 (by rw [← hp' φ hφ, h]; rfl)⟩
  have onto : (SB _).map p = ⊤ := map_eq_top _ _ hI p (fun φ hφ x => by
    obtain ⟨φ₁, h1, h2⟩ := hb.surjOn (GlobalTheory.SplitFlip.omA_mem_SB (α / β) β 1 x (m φ hφ))
    exact ⟨φ₁, h1, funext fun y => by rw [hp _ h1, hp _ hφ, h2, mapA_omA_right]⟩) ne
  have onto' : (SB _).map p' = ⊤ := map_eq_top _ _ hI p' (fun φ hφ x => by
    obtain ⟨φ₁, h1, h2⟩ := hb'.surjOn (GlobalTheory.SplitFlip.omB_mem_SB (α / β) α 1 x (m' φ hφ))
    exact ⟨φ₁, h1, funext fun y => by rw [hp' _ h1, hp' _ hφ, h2, mapB_omB_right]⟩) ne'
  let R : FinMaps F a a' :=
    { Pi := fun _ => indSp a a' α β
      grp := fun _ => inferInstance
      mod := fun _ => inferInstance
      p := Function.update (fun _ => 0) v p
      p' := Function.update (fun _ => 0) v p' }
  have e : R.p v = p := by simp only [R, Function.update_self]
  have e' : R.p' v = p' := by simp only [R, Function.update_self]
  refine ⟨R, Subtype.val, Subtype.val_injective, rfl, by rw [e]; exact hp, by rw [e']; exact hp', fun h1 h2 => ?_⟩
  refine ⟨by rw [e]; exact onto, by rw [e']; exact onto', ?_, ?_, ?_, ?_, ?_, h1, h2⟩
  · rw [e]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, H, rfl⟩
    refine LinearMap.mem_ker.2 ?_
    rw [map_sub, sub_eq_zero]
    refine Subtype.ext ?_
    rw [hp _ hφ₁, hp _ hφ, act g hg 1 (one_mem_UAt _ v) φ hφ φ₁ hφ₁ H, map_one, mapA_omA_left hl _ (m φ hφ)]
  · rw [e']
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, H, rfl⟩
    refine LinearMap.mem_ker.2 ?_
    rw [map_sub, sub_eq_zero]
    refine Subtype.ext ?_
    rw [hp' _ hφ₁, hp' _ hφ, act' g hg 1 (one_mem_UAt _ v) φ hφ φ₁ hφ₁ H, map_one, mapB_omB_left hl' _ (m' φ hφ)]
  · rw [e, e']
    intro h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' H H' heq
    refine Subtype.ext ?_
    rw [tr h hh φ hφ φ₁ hφ₁ H, tr' h hh φ' hφ' φ₁' hφ₁' H', heq]
  · obtain ⟨φ, -, h0⟩ := ne
    exact ⟨⟨p φ, 0, h0⟩⟩
  · rw [e]
    intro N hN
    rcases hI (Submodule.map (indSp a a' α β).subtype N) (Submodule.map_subtype_le _ _) (by
      rintro _ ⟨f, hf, rfl⟩ x
      obtain ⟨φ, hφ, rfl⟩ : f ∈ (SB _).map p := onto ▸ Submodule.mem_top
      obtain ⟨h, hh, rfl⟩ := GlobalTheory.T.local_unitary_matrix_surjective F E σ B _ G.W _ _ hT.base hT.geo.hW v t c x
      obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_big hT) v).1 1
        (one_mem_UAt _ v) h hh φ hφ
      exact ⟨p φ₁, hN h hh φ hφ φ₁ h1 H hf, tr h hh φ hφ φ₁ h1 H⟩) with h | h
    · exact Or.inl (Submodule.map_injective_of_injective (indSp a a' α β).injective_subtype
        (h.trans (Submodule.map_bot _).symm))
    · exact Or.inr (Submodule.map_injective_of_injective (indSp a a' α β).injective_subtype
        (h.trans (Submodule.map_subtype_top _).symm))

theorem indicator_eq {v : Pl F} {m n : Type} :
    {Y : Matrix m n (Fv F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} = intM (Fv F v) m n := by
  ext Y
  simp only [intM, Set.mem_setOf_eq, GlobalTheory.FinPl.SplitPoint.mem_integer_iff]

theorem finMapsAt_split : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityGL →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Nonempty (E →ₐ[F] Fv F v) → ∃ R : FinMaps F a a', FinMapsAt B G X om om' R v := by
  intro hP _ F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨t₀⟩
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  by_cases hv : v ∈ X.T
  · have hvP : v ∈ B.P := hT.chars.sub hv
    set t := B.τ ⟨v, hvP⟩ with ht
    obtain ⟨ι, hι, hvac⟩ := GlobalTheory.T.split_basis_witt_model_local hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_big hT) v t _ _
      (hT.geo.hV.bas ⟨v, hvP⟩) (hT.geo.hW.bas ⟨v, hvP⟩)
    obtain ⟨b₁, hb₁, ι', hι', hvac'⟩ := GlobalTheory.T.split_basis_witt_model_equivariant hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (isPair_small hT) v t _ _
      (hT.geo.hV'.bas ⟨v, hvP⟩) (hT.geo.hW.bas ⟨v, hvP⟩)
    rw [hb₁ (hT.base.psiP v hvP)] at hι'
    have hν : chrW X.ν t = chrW X.α t / chrW X.β t := chrW_div _ _ t
    obtain ⟨hs, ⟨e, he⟩, hr⟩ := GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.ν (isHecke_div hT.chars.heckeα hT.chars.heckeβ) v t
    have hram : ¬ GlobalTheory.SplitWeil.IsUnram (chrW X.ν t) :=
      fun h => hT.chars.ram (splitPrime t) (by rw [splitPrime_under]; exact hv) (hr.1 h)
    obtain ⟨hl, hl0⟩ := GlobalTheory.T.shell_sum_equivariant_nonzero (Fv F v) (unifAt v) a e _ (((a + a' : ℕ) : ℂ) / 2)
      (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec hs hram he
    obtain ⟨hl', hl0'⟩ := GlobalTheory.T.zeta_integral_equivariant_nonzero (Fv F v) a' _ (((a + a' : ℕ) : ℂ) / 2) hs (by
      have : (a' : ℝ) < a := by exact_mod_cast hT.geo.lt
      simp only [Complex.div_ofNat_re, Complex.natCast_re]
      push_cast
      linarith)
    rw [hν] at hl hl0 hl' hl0'
    obtain ⟨R, j, hj, -, h1, h2, H⟩ := core hP hT t hι hι' hl hl0 hl' hl0'
    refine ⟨R, H (fun h => absurd hv h) fun _ _ => ⟨ι, ι', hι, hι', hvac, hvac', fun φ hφ φ' hφ' => ?_⟩⟩
    rw [← hj.eq_iff, h1 φ hφ, h2 φ' hφ', ← hν]
    refine Eq.congr ?_ ?_
    · funext h
      simp only [mapA, GlobalTheory.SplitFlip.bigP, GlobalTheory.SplitFlip.bigF, Fintype.card_fin]
      rfl
    · funext h
      rw [GlobalTheory.SplitFlip.smallP_eq]
      simp only [mapB, GlobalTheory.SplitFlip.smallF, Fintype.card_fin]
      rfl
  · haveI := hT.geo.hV.lat
    haveI := hT.geo.hV'.lat
    haveI := hT.geo.hW.lat
    obtain ⟨b, hb⟩ := exists_isSplitBasis t₀ G.V.L hT.base.cm
    obtain ⟨b', hb'⟩ := exists_isSplitBasis t₀ G.V'.L hT.base.cm
    obtain ⟨c, hc⟩ := exists_isSplitBasis t₀ G.W.L hT.base.cm
    obtain ⟨ι, hι, hvac⟩ := GlobalTheory.T.split_basis_witt_model_local hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_big hT) v t₀ b c hb hc
    obtain ⟨b₁, -, ι', hι', hvac'⟩ := GlobalTheory.T.split_basis_witt_model_equivariant hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (isPair_small hT) v t₀ b' c hb' hc
    rw [indicator_eq] at hvac hvac'
    obtain ⟨hα, -, hrα⟩ := GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hT.chars.heckeα v t₀
    obtain ⟨hβ, -, hrβ⟩ := GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hT.chars.heckeβ v t₀
    have hw : splitPrime t₀ ∉ above E (X.T : Set (Pl F)) := by
      show ¬ (splitPrime t₀).under (𝓞 F) ∈ (X.T : Set (Pl F))
      rw [splitPrime_under]
      exact hv
    have uα := hrα.2 (hT.chars.unrα _ hw)
    have uβ := hrβ.2 (hT.chars.unrβ _ hw)
    have uν : GlobalTheory.SplitWeil.IsUnram (chrW X.α t₀ / chrW X.β t₀) := fun x hx => by
      rw [MonoidHom.div_apply, uα x hx, uβ x hx, div_one]
    obtain ⟨l, hl, hl1⟩ := GlobalTheory.T.unramified_character_normalized_equivariant_functional (Fv F v) a _ (((a + a' : ℕ) : ℂ) / 2) (hα.div hβ) uν
    obtain ⟨l', hl', hl1'⟩ := GlobalTheory.T.unramified_character_normalized_equivariant_functional (Fv F v) a' _ (((a + a' : ℕ) : ℂ) / 2) (hα.div hβ) uν
    obtain ⟨R, j, hj, hj0, h1, h2, H⟩ := core hP hT t₀ hι hι' hl ⟨_, indicator_intM_mem_SB, hl1 ▸ one_ne_zero⟩
      hl' ⟨_, indicator_intM_mem_SB, hl1' ▸ one_ne_zero⟩
    refine ⟨R, H (fun _ => ?_) fun _ h => absurd h hv⟩
    have e1 := h1 _ (hT.geo.hM.vac v).1
    have e2 := h2 _ (hT.geo.hM'.vac v).1
    rw [hvac] at e1
    rw [hvac'] at e2
    have u1 := mapA_unit (a' := a') (ν := chrW X.α t₀ / chrW X.β t₀) uβ l
    have u2 := mapB_unit (a := a) (ν := chrW X.α t₀ / chrW X.β t₀) uα l'
    refine ⟨hj ?_, fun h => ?_⟩
    · rw [e1, e2, ← sub_eq_zero]
      refine GlobalTheory.T.induced_spherical_vanishing_at_identity _ a a' _ _ _ (sub_mem (GlobalTheory.T.intertwining_map_into_induced_left _ a a' _ _ l hβ hl _ indicator_intM_mem_SB)
        (GlobalTheory.T.intertwining_map_into_induced_right _ a a' _ _ l' hα hl' _ indicator_intM_mem_SB)) (fun u hu h => ?_) ?_
      · rw [Pi.sub_apply, Pi.sub_apply, u1.1 u hu, u2.1 u hu]
      · rw [Pi.sub_apply, u1.2, u2.2, hl1, hl1', sub_self]
    · rw [h, hj0] at e1
      have := congrFun e1 1
      rw [u1.2, hl1] at this
      exact zero_ne_one this

end Adelic

end GlobalTheory.KSplit

end
