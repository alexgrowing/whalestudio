import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TensorLatticeUnitPart
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR

noncomputable section

namespace GlobalTheory.Cmp.WachMonoidal

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke

section Ext

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']

theorem extMul_eq (b : M →ₗ[O] M' →ₗ[O] M'') (u : R ⊗[O] M) (w : R ⊗[O] M') :
    UnitDualParts.extMul R (TensorProduct.lift b) u w = TensorLatticeUnitPart.extBil R b u w := by
  induction u using TensorProduct.induction_on with
  | zero => simp [UnitDualParts.extMul, TensorLatticeUnitPart.extBil]
  | add x y hx hy =>
    simp only [UnitDualParts.extMul, TensorLatticeUnitPart.extBil, add_tmul, map_add] at hx hy ⊢
    rw [hx, hy]
  | tmul r a =>
    induction w using TensorProduct.induction_on with
    | zero => simp [UnitDualParts.extMul, TensorLatticeUnitPart.extBil]
    | add x y hx hy =>
      simp only [UnitDualParts.extMul, TensorLatticeUnitPart.extBil, tmul_add, map_add] at hx hy ⊢
      rw [hx, hy]
    | tmul r' a' => rw [UnitDualParts.extMul_tmul, TensorLatticeUnitPart.extBil_tmul, TensorProduct.lift.tmul]

theorem extPair_eq (b : M →ₗ[O] M' →ₗ[O] O) (u : R ⊗[O] M) (w : R ⊗[O] M') :
    UnitDualParts.extPair R b u w = TensorLatticeUnitPart.extForm R b u w := by
  rw [UnitDualParts.extPair, TensorLatticeUnitPart.extForm, extMul_eq]

end Ext

section Crys

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem tensorB_comp (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) g (CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x) =
      CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (g.comp f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem tensorB_id (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (LinearMap.id : V →ₗ[LL] V) x = x := by
  simp [CrystallineSubrepresentation.tensorB]

theorem tensorB_zero (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (0 : V →ₗ[LL] V') x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

theorem tensorB_add (f g : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (f + g) x =
      CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x + CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB, add_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]; abel

theorem coe_DcrisMap {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : CrystallineSubrepresentation.IsEquivariant ρ ρ' f) (x : ↥(Dcris PD ρ)) :
    (CrystallineSubrepresentation.DcrisMap PD hf x : V' ⊗[Qp] B) = CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x := rfl

theorem isCrys_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  have h1 : CrystallineSubrepresentation.IsEquivariant ρ ρ' e.toLinearMap := he
  have h2 : CrystallineSubrepresentation.IsEquivariant ρ' ρ e.symm.toLinearMap := fun g x => by
    apply e.injective
    simp [he]
  let E : ↥(Dcris PD ρ) ≃ₗ[LL] ↥(Dcris PD ρ') :=
    LinearEquiv.ofLinear (CrystallineSubrepresentation.DcrisMap PD h1) (CrystallineSubrepresentation.DcrisMap PD h2)
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
  unfold IsCrys at h ⊢
  rw [← E.finrank_eq, ← e.finrank_eq, h]

theorem finite_Dcris [FiniteDimensional LL V] {ρ : Representation LL G V} (h : IsCrys PD ρ) :
    Module.Finite LL ↥(Dcris PD ρ) := by
  rcases Nat.eq_zero_or_pos (finrank LL ↥(Dcris PD ρ)) with h0 | h0
  · have := PD.finK₀
    have hK : 0 < finrank Qp K₀ := Module.finrank_pos
    unfold IsCrys at h
    have hV : finrank LL V = 0 := by
      rw [h0] at h
      rcases Nat.mul_eq_zero.mp h.symm with h | h
      · omega
      · exact h
    have : Subsingleton V := Module.finrank_zero_iff.mp hV
    infer_instance
  · exact Module.finite_of_finrank_pos h0

theorem isCrys_prod [FiniteDimensional LL V] [FiniteDimensional LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (h : IsCrys PD ρ) (h' : IsCrys PD ρ') : IsCrys PD (ρ.prod ρ') := by
  have := finite_Dcris PD h
  have := finite_Dcris PD h'
  have e1 : CrystallineSubrepresentation.IsEquivariant ρ (ρ.prod ρ') (LinearMap.inl LL V V') := fun g x => by
    simp [Representation.prod]
  have e2 : CrystallineSubrepresentation.IsEquivariant ρ' (ρ.prod ρ') (LinearMap.inr LL V V') := fun g x => by
    simp [Representation.prod]
  have p1 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ (LinearMap.fst LL V V') := fun g x => by
    simp [Representation.prod]
  have p2 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ' (LinearMap.snd LL V V') := fun g x => by
    simp [Representation.prod]
  let E : (↥(Dcris PD ρ) × ↥(Dcris PD ρ')) ≃ₗ[LL] ↥(Dcris PD (ρ.prod ρ')) :=
    LinearEquiv.ofLinear ((CrystallineSubrepresentation.DcrisMap PD e1).coprod (CrystallineSubrepresentation.DcrisMap PD e2))
      ((CrystallineSubrepresentation.DcrisMap PD p1).prod (CrystallineSubrepresentation.DcrisMap PD p2))
      (by
        refine LinearMap.ext fun x => Subtype.ext ?_
        simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
          Submodule.coe_add, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [← tensorB_add, show (LinearMap.inl LL V V').comp (LinearMap.fst LL V V') +
          (LinearMap.inr LL V V').comp (LinearMap.snd LL V V') = LinearMap.id by ext <;> simp,
          tensorB_id])
      (by
        refine LinearMap.ext fun x => Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, tensorB_id, tensorB_zero, add_zero]
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, tensorB_id, tensorB_zero, zero_add])
  unfold IsCrys at h h' ⊢
  rw [← E.finrank_eq, Module.finrank_prod, Module.finrank_prod, h, h', mul_add]

end Crys

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem isSumLat_iff {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) :
    UnitDualParts.IsSumLat i i' ↔ TensorLatticeUnitPart.IsSumLat i i' := Iff.rfl

theorem isTensorLat_curry {T T' T'' : LocLat G Qp LL O} (m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T)
    (hm : UnitDualParts.IsTensorLat m) :
    TensorProduct.lift (TensorProduct.curry m.toLinearMap) = m.toLinearMap ∧
      TensorLatticeUnitPart.IsTensorLat (TensorProduct.curry m.toLinearMap) := by
  have h : TensorProduct.lift (TensorProduct.curry m.toLinearMap) = m.toLinearMap := by
    ext x y; simp
  refine ⟨h, ?_, fun g x y => hm g x y⟩
  rw [h]
  exact m.bijective

theorem isTensorLat_ofBijective {T T' T'' : LocLat G Qp LL O}
    (b : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] ↥T''.L.T) (hb : TensorLatticeUnitPart.IsTensorLat b) :
    UnitDualParts.IsTensorLat (LinearEquiv.ofBijective (TensorProduct.lift b) hb.1) := fun g x y => by
  simpa using hb.2 g x y

theorem isCrys_of_isSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L)
    (i' : LatHom T'.L T''.L) (h : IsCrys PD T.ρ) (h' : IsCrys PD T'.ρ) (hs : TensorLatticeUnitPart.IsSumLat i i') :
    IsCrys PD T''.ρ :=
  isCrys_of_equiv PD (LinearEquiv.ofBijective (i.f.coprod i'.f) hs.1)
    (fun g x => by simp [Representation.prod, i.equiv, i'.equiv]) (isCrys_prod PD h h')

variable (PD LL O) in

def TensorLatCrys : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (b : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] ↥T''.L.T),
    IsCrys PD T.ρ → IsCrys PD T'.ρ → TensorLatticeUnitPart.IsTensorLat b → IsCrys PD T''.ρ

variable (PD LL O) in

def DualLatCrys : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL),
    IsCrys PD T.ρ → IsDualLat T.L T'.L Pr → IsCrys PD T'.ρ

theorem isBaseChange_lat [IsFractionRing O LL] (T : LocLat G Qp LL O) :
    IsBaseChange LL T.L.T.subtype := by
  rw [← isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) LL]
  refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩⟩
  · have := (IsLocalization.map_units LL s).map (algebraMap LL (Module.End LL T.V))
    rw [Module.End.isUnit_iff] at this ⊢
    convert this using 1
    ext x
    simp
  · have hy : y ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
    have : ∃ s : nonZeroDivisors O, (s : O) • y ∈ T.L.T := by
      induction hy using Submodule.span_induction with
      | mem x hx => exact ⟨1, by simpa using hx⟩
      | zero => exact ⟨1, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        refine ⟨s * t, ?_⟩
        rw [smul_add, Submonoid.coe_mul]
        refine T.L.T.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact T.L.T.smul_mem _ hs
        · rw [mul_smul]; exact T.L.T.smul_mem _ ht
      | smul c x _ hx =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨⟨a, t⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors O) c
        refine ⟨s * t, ?_⟩
        have : ((s * t : nonZeroDivisors O) : O) • c • x = a • (s : O) • x := by
          rw [← algebraMap_smul LL a, ← algebraMap_smul LL (s : O),
            ← algebraMap_smul LL ((s * t : nonZeroDivisors O) : O), smul_smul, smul_smul,
            Submonoid.coe_mul, map_mul]
          simp only at hc
          rw [← hc]
          congr 1
          ring
        rw [this]
        exact T.L.T.smul_mem _ hs
    obtain ⟨s, hs⟩ := this
    exact ⟨(⟨_, hs⟩, s), rfl⟩

theorem tensorLatCrys_of [IsFractionRing O LL] (h : CrystallineSubrepresentation.TensorCrys PD LL) :
    TensorLatCrys PD LL O := by
  intro T T' T'' b hT hT' hb
  let e : T.V ⊗[LL] T'.V ≃ₗ[LL] T''.V :=
    (TensorProduct.congr (isBaseChange_lat T).equiv.symm (isBaseChange_lat T').equiv.symm).trans
      ((AlgebraTensorModule.distribBaseChange O LL ↥T.L.T ↥T'.L.T).symm.trans
        (((LinearEquiv.ofBijective (TensorProduct.lift b) hb.1).baseChange O LL _ _).trans
          (isBaseChange_lat T'').equiv))
  have he : ∀ (x : ↥T.L.T) (y : ↥T'.L.T), e ((x : T.V) ⊗ₜ[LL] (y : T'.V)) = (b x y : T''.V) := by
    intro x y
    have hx : (isBaseChange_lat T).equiv.symm (x : T.V) = 1 ⊗ₜ[O] x :=
      (isBaseChange_lat T).equiv_symm_apply x
    have hy : (isBaseChange_lat T').equiv.symm (y : T'.V) = 1 ⊗ₜ[O] y :=
      (isBaseChange_lat T').equiv_symm_apply y
    simp [e, hx, hy, IsBaseChange.equiv_tmul]
  refine isCrys_of_equiv PD e (fun g z => ?_) (h T.V T.ρ T'.V T'.ρ hT hT')
  have key : TensorProduct.curry (e.toLinearMap.comp ((T.ρ.tprod T'.ρ) g)) =
      TensorProduct.curry ((T''.ρ g).comp e.toLinearMap) := by
    refine LinearMap.ext_on T.L.span fun x hx => LinearMap.ext_on T'.L.span fun y hy => ?_
    have h1 := he (T.actT g ⟨x, hx⟩) (T'.actT g ⟨y, hy⟩)
    have h2 := he ⟨x, hx⟩ ⟨y, hy⟩
    rw [hb.2] at h1
    change e (T.ρ g x ⊗ₜ[LL] T'.ρ g y) = T''.ρ g (e (x ⊗ₜ[LL] y))
    rw [h2]
    exact h1
  exact LinearMap.congr_fun (TensorProduct.curry_injective key) z

theorem dualLatCrys_of (h : CrystallineSubrepresentation.DualCrys PD LL) : DualLatCrys PD LL O := by
  rintro T T' Pr hT ⟨hG, -, h2, hr, -⟩
  have hinj : Function.Injective Pr.flip := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y fun x => LinearMap.congr_fun hy x
  have hbij : Function.Bijective Pr.flip :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [← hr]; exact (Subspace.dual_finrank_eq (K := LL) (V := T.V)).symm)).mp hinj⟩
  let e : T'.V ≃ₗ[LL] Module.Dual LL T.V := LinearEquiv.ofBijective Pr.flip hbij
  refine isCrys_of_equiv PD e.symm (fun g f => ?_) (h T.V T.ρ hT)
  obtain ⟨y, rfl⟩ := e.surjective f
  apply e.injective
  rw [e.apply_symm_apply, e.symm_apply_apply]
  ext x
  change Pr (T.ρ g⁻¹ x) y = Pr x (T'.ρ g y)
  rw [← hG g]
  simp

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unit_iff (E : EtTie W RA RW inclR φR gR πA) : UnitDualParts.UnitFor E ↔ TensorLatticeUnitPart.UnitAt W E :=
  Iff.rfl

theorem sum_iff : UnitDualParts.SumFor W ↔ TensorLatticeUnitPart.SumAt W := by
  constructor
  · intro h T T' T'' i i' hT hT' hs
    obtain ⟨σ, h1, h2, h3, h4⟩ := h T T' T'' hT hT' i i' hs
    refine ⟨isCrys_of_isSumLat i i' hT hT' hs, ?_, fun x y => ?_, fun g x y => ?_, fun z => ?_⟩
    · have : ⇑((W.map i).coprod (W.map i')) = σ := by
        funext p
        exact (h1 p.1 p.2).symm
      rw [this]
      exact σ.bijective
    · rw [← h1, ← h1, h2]
    · rw [← h1, ← h1, h3]
    · constructor
      · intro hz
        obtain ⟨⟨x, y⟩, rfl⟩ := σ.surjective z
        exact ⟨x, ((h4 x y).mp hz).1, y, ((h4 x y).mp hz).2, h1 x y⟩
      · rintro ⟨x, hx, y, hy, rfl⟩
        rw [← h1]
        exact (h4 x y).mpr ⟨hx, hy⟩
  · intro h T T' T'' hT hT' i i' hs
    obtain ⟨-, h1, h2, h3, h4⟩ := h T T' T'' i i' hT hT' hs
    refine ⟨LinearEquiv.ofBijective _ h1, fun x y => rfl, h2, h3, fun x y => ?_⟩
    refine (h4 _).trans ⟨?_, fun h => ⟨x, h.1, y, h.2, rfl⟩⟩
    rintro ⟨x', hx', y', hy', hxy⟩
    have : (x, y) = (x', y') := h1.1 hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
    exact ⟨hx', hy'⟩

theorem tensor_iff (E : EtTie W RA RW inclR φR gR πA) :
    TensorLatticeUnitPart.TensorAt W E ↔ UnitDualParts.TensorFor E ∧ TensorLatCrys PD LL O := by
  constructor
  · intro h
    refine ⟨fun T T' T'' hT hT' m hm => ?_, fun T T' T'' b hT hT' hb => (h T T' T'' b hT hT' hb).1⟩
    obtain ⟨hl, hb⟩ := isTensorLat_curry m hm
    obtain ⟨-, β, h1, h2, h3, h4, -, βN, h5, h6⟩ := h T T' T'' _ hT hT' hb
    refine ⟨β, fun x y => ?_, h2, h3, h4, LinearEquiv.ofBijective _ h6, fun x y => ?_⟩
    · rw [h1, ← extMul_eq, hl]
    · rw [← h5]
      simp
  · rintro ⟨h, hc⟩ T T' T'' b hT hT' hb
    obtain ⟨μ, h1, h2, h3, h4, ν, hν⟩ := h T T' T'' hT hT' _ (isTensorLat_ofBijective b hb)
    refine ⟨hc T T' T'' b hT hT' hb, μ, fun x y => ?_, h2, h3, h4, ?_,
      TensorProduct.curry ν.toLinearMap, fun x y => hν x y, ?_⟩
    · rw [h1, ← extMul_eq]
      rfl
    · apply le_antisymm
      · intro z hz
        obtain ⟨w, hw⟩ := ν.surjective ⟨z, hz⟩
        have hz' : z = ((ν w : ↥(W.N T'')) : W.DD T'') := by rw [hw]
        rw [hz']
        clear hw hz' hz
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => rw [hν]; exact Submodule.subset_span ⟨x, x.2, y, y.2, rfl⟩
        | add a b ha hb => rw [map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hb
      · rw [Submodule.span_le]
        rintro z ⟨x, hx, y, hy, rfl⟩
        have := hν ⟨x, hx⟩ ⟨y, hy⟩
        simp only at this
        rw [← this]
        exact (ν _).2
    · have : TensorProduct.lift (TensorProduct.curry ν.toLinearMap) = ν.toLinearMap := by
        ext x y; simp
      rw [this]
      exact ν.bijective

theorem exists_dualEquiv {A R D D' : Type} [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup D] [Module R D] [Module A D] [IsScalarTower A R D]
    [AddCommGroup D'] [Module R D'] [Module A D'] [IsScalarTower A R D']
    (hinj : Function.Injective (algebraMap A R)) (N : Submodule A D) (N' : Submodule A D')
    (b : D →ₗ[R] D' →ₗ[R] R) (hv : ∀ y ∈ N', ∀ x ∈ N, ∃ a : A, b x y = algebraMap A R a)
    (hi : ∀ y, (∀ x ∈ N, b x y = 0) → y = 0)
    (hs : ∀ f : ↥N →ₗ[A] A, ∃ y ∈ N', ∀ x : ↥N, b (x : D) y = algebraMap A R (f x)) :
    ∃ δ : ↥N' ≃ₗ[A] Module.Dual A ↥N,
      ∀ (x : ↥N) (y : ↥N'), b (x : D) (y : D') = algebraMap A R (δ y x) := by
  choose c hc using hv
  have hl : ∀ (a : A) (x : D) (y : D'), b (a • x) y = algebraMap A R a * b x y := by
    intro a x y
    rw [← algebraMap_smul R a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hr : ∀ (a : A) (x : D) (y : D'), b x (a • y) = algebraMap A R a * b x y := by
    intro a x y
    rw [← algebraMap_smul R a y, map_smul, smul_eq_mul]
  let d : ↥N' →ₗ[A] ↥N →ₗ[A] A := LinearMap.mk₂ A (fun y x => c y y.2 x x.2)
    (fun y y' x => hinj (by rw [map_add, ← hc, ← hc, ← hc, Submodule.coe_add, map_add]))
    (fun a y x => hinj (by rw [smul_eq_mul, map_mul, ← hc, ← hc, Submodule.coe_smul, hr]))
    (fun y x x' => hinj (by
      rw [map_add, ← hc, ← hc, ← hc, Submodule.coe_add, map_add, LinearMap.add_apply]))
    (fun a y x => hinj (by rw [smul_eq_mul, map_mul, ← hc, ← hc, Submodule.coe_smul, hl]))
  have hd : ∀ (x : ↥N) (y : ↥N'), b (x : D) (y : D') = algebraMap A R (d y x) :=
    fun x y => hc y y.2 x x.2
  refine ⟨LinearEquiv.ofBijective d ⟨?_, fun f => ?_⟩, hd⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    refine Subtype.ext (hi y fun x hx => ?_)
    rw [hd ⟨x, hx⟩ y, hy, LinearMap.zero_apply, map_zero]
  · obtain ⟨y, hy, hf⟩ := hs f
    refine ⟨⟨y, hy⟩, LinearMap.ext fun x => hinj ?_⟩
    rw [← hd, hf]

theorem dual_iff (E : EtTie W RA RW inclR φR gR πA) :
    TensorLatticeUnitPart.DualAt W E ↔ UnitDualParts.DualFor E ∧ DualLatCrys PD LL O := by
  constructor
  · intro h
    refine ⟨fun T T' hT Pr hP => ?_, fun T T' Pr hT hP => (h T T' Pr hT hP).1⟩
    obtain ⟨-, PT, h0, β, h1, h2, h2', h3, h4, h5, h6⟩ := h T T' Pr hT hP
    refine ⟨PT, β, fun x y => (h0 x y).symm, fun x y => by rw [h1, extPair_eq], h2, h2', h3, h4, h5,
      exists_dualEquiv W.EE_inj _ _ β (fun y hy => (h5 y).mp hy) (fun y hy => ?_) h6⟩
    apply h2'.1
    rw [map_zero]
    exact (W.N_base T hT).algHom_ext _ _ fun x => hy x x.2
  · rintro ⟨h, hc⟩ T T' Pr hT hP
    obtain ⟨PT, β, h0, h1, h2, h2', h3, h4, h5, δ, hδ⟩ := h T T' hT Pr hP
    refine ⟨hc T T' Pr hT hP, PT, fun x y => (h0 x y).symm, β,
      fun x y => by rw [h1, extPair_eq], h2, h2', h3, h4, h5, fun f => ?_⟩
    obtain ⟨y, rfl⟩ := δ.surjective f
    exact ⟨y, y.2, fun x => hδ x y⟩

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

def TensorDualCrys : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL →
    TensorLatCrys (P.PD K) ↥LL.1 ↥(OL LL) ∧ DualLatCrys (P.PD K) ↥LL.1 ↥(OL LL)

theorem tensorDualCrys_of (hT : CrystallineSubrepresentation.LocTensorCrys l P) (hD : CrystallineSubrepresentation.LocDualCrys l P) :
    TensorDualCrys l P := fun K _ LL _ => by
  obtain ⟨_, -, -, -, -, -, hF⟩ := GlobalTheory.Per.integers_completeDVR l LL
  exact ⟨tensorLatCrys_of (hT K LL), dualLatCrys_of (hD K LL)⟩

theorem unitPart_iff : UnitDualParts.UnitPart l P AI H F ↔ TensorLatticeUnitPart.UnitPart l P AI H F := Iff.rfl

theorem sumPart_iff : UnitDualParts.SumPart l P H ↔ TensorLatticeUnitPart.SumPart l P H :=
  ⟨fun h K s LL hg => sum_iff.mp (h K s LL hg), fun h K s LL hg => sum_iff.mpr (h K s LL hg)⟩

theorem wachMonoidal_iff :
    TensorLatticeUnitPart.WachMonoidal l P AI H F ↔ UnitDualParts.UnitSumTensorDual l P AI H F ∧ TensorDualCrys l P := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, (sumPart_iff l P H).mpr h2,
      fun K s LL hg => ((tensor_iff _).mp (h3 K s LL hg)).1,
      fun K s LL hg => ((dual_iff _).mp (h4 K s LL hg)).1⟩,
      fun K s LL hg => ⟨((tensor_iff _).mp (h3 K s LL hg)).2, ((dual_iff _).mp (h4 K s LL hg)).2⟩⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, hc⟩
    exact ⟨h1, (sumPart_iff l P H).mp h2,
      fun K s LL hg => (tensor_iff _).mpr ⟨h3 K s LL hg, (hc K s LL hg).1⟩,
      fun K s LL hg => (dual_iff _).mpr ⟨h4 K s LL hg, (hc K s LL hg).2⟩⟩

theorem unitSumTensorDual_of_wachMonoidal (h : TensorLatticeUnitPart.WachMonoidal l P AI H F) :
    UnitDualParts.UnitSumTensorDual l P AI H F :=
  ((wachMonoidal_iff l P AI H F).mp h).1

theorem equiv_of_stability (hT : CrystallineSubrepresentation.LocTensorCrys l P) (hD : CrystallineSubrepresentation.LocDualCrys l P) :
    UnitDualParts.UnitSumTensorDual l P AI H F ↔ TensorLatticeUnitPart.WachMonoidal l P AI H F :=
  ⟨fun h => (wachMonoidal_iff l P AI H F).mpr ⟨h, tensorDualCrys_of l P hT hD⟩,
    unitSumTensorDual_of_wachMonoidal l P AI H F⟩

end GlobalTheory.Cmp.WachMonoidal
