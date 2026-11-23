import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

open Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.ConjCrys

section DdR

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem ddR_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ DdR PD ρ, GlobalTheory.HTW.SumJumps.ext1 Qp BdR f x ∈ DdR PD ρ' := by
  intro x hx
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := hx g
  unfold actVdR at this ⊢
  rw [GlobalTheory.HTW.SumJumps.ext1_comm f (ρ g) (ρ' g) (hf g), this]

theorem finrank_ddR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (DdR PD ρ) = finrank LL (DdR PD ρ') :=
  GlobalTheory.HTW.Rec.finrank_eq_of_equiv_tensor e _ _ (ddR_map PD e.toLinearMap he)
    (ddR_map PD e.symm.toLinearMap (GlobalTheory.HTW.Rec.symm_equivariant e he))

end DdR

section Matrix

theorem mapRep_conj {Γ : Type} [Group Γ] {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S)
    (M : GL (Fin a) R) (ρ : Γ →* GL (Fin a) R) :
    mapRep f ((MulAut.conj M).toMonoidHom.comp ρ) =
      (MulAut.conj (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) R →+* Matrix (Fin a) (Fin a) S).toMonoidHom M)).toMonoidHom.comp
        (mapRep f ρ) := by
  ext g : 1
  simp [mapRep, MulAut.conj_apply, map_mul, map_inv]

variable {l : ℕ} [Fact l.Prime]

def glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) : GL (Fin n) ↥L.1 where
  val := Matrix.of fun i j => ⟨_, (hA i j).1⟩
  inv := Matrix.of fun i j => ⟨_, (hA i j).2⟩
  val_inv := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.inv_mul

theorem map_glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) :
    Units.map ((algebraMap ↥L.1 (Om l)).mapMatrix :
      Matrix (Fin n) (Fin n) ↥L.1 →+* Matrix (Fin n) (Fin n) (Om l)).toMonoidHom (glOf L A hA) = A := by
  ext i j
  rfl

end Matrix

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  (Bw : LocBridge l E Ω Gw O) {m : ℕ}

def linOf {L : Type} [Field L] (M : GL (Fin m) L) : (Fin m → L) ≃ₗ[L] (Fin m → L) :=
  LinearEquiv.ofLinear (Matrix.toLin' (M : Matrix (Fin m) (Fin m) L))
    (Matrix.toLin' ((M⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L))
    (by rw [← Matrix.toLin'_mul, M.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, M.inv_mul, Matrix.toLin'_one])

theorem linOf_repE (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) (g) (v : Fin m → ↥L.1) :
    linOf M (Bw.repE L ((MulAut.conj M⁻¹).toMonoidHom.comp r) g v) = Bw.repE L r g (linOf M v) := by
  simp only [linOf, LocBridge.repE, LinearEquiv.ofLinear_apply, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.coeHom_apply, Matrix.toLin'_apply, inv_inv, Units.val_mul]
  erw [Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, M.mul_inv, Matrix.one_mul]

theorem local_conj (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) :
    (Bw.IsCrysE P L r → Bw.IsCrysE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    (Bw.IsdRE P L r → Bw.IsdRE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    ∀ τ a, Bw.multE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r) τ a = Bw.multE P L r τ a := by
  have he := linOf_repE Bw L M r
  refine ⟨fun h => GlobalTheory.HTW.Rec.isCrys_of_equiv _ (linOf M) he h, fun h => ?_, fun τ a =>
    GlobalTheory.HTW.Rec.multV_eq_of_equiv _ (linOf M) he τ a⟩
  unfold LocBridge.IsdRE at h ⊢
  rw [finrank_ddR_eq_of_equiv _ (linOf M) he, h]

variable {P Bw}

theorem exists_conj_model {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {LL' : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥LL'.1} (hm : GlobalTheory.Pst.IsModel Bw r LL' r') :
    ∃ (h : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1) (M : GL (Fin m) ↥(GlobalTheory.Pst.supExt LL' K).1),
      GlobalTheory.Pst.IsModel Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) (GlobalTheory.Pst.supExt LL' K)
        ((MulAut.conj M⁻¹).toMonoidHom.comp (mapRep (IntermediateField.inclusion h).toRingHom r')) := by
  have h1 : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_left
  have h2 : K.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_right
  have hA' : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 :=
    fun i j => ⟨h2 (hA i j).1, h2 (hA i j).2⟩
  have hm2 := hm.enlarge h1
  refine ⟨h1, glOf _ A hA', hm2.1, ?_⟩
  rw [mapRep_conj, hm2.2, map_inv, map_glOf]

theorem isCrysAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    (hr : GlobalTheory.Pst.IsCrysAt P Bw r) : GlobalTheory.Pst.IsCrysAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r', hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  exact ⟨_, _, hM, (local_conj P Bw _ M _).1 ((GlobalTheory.Pst.local_ext P Bw h r').1.2 hc)⟩

theorem isJumpsAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {τ : E →+* Om l} {J : Multiset ℤ}
    (hr : GlobalTheory.Pst.IsJumpsAt P Bw r τ J) : GlobalTheory.Pst.IsJumpsAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) τ J := by
  obtain ⟨LL', r', hm, hdR, τ', hI, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, hmult⟩ := GlobalTheory.Pst.local_ext P Bw h r'
  obtain ⟨-, hdR3, hmult3⟩ := local_conj P Bw _ M (mapRep (IntermediateField.inclusion h).toRingHom r')
  refine ⟨_, _, hM, hdR3 (hdR2.2 hdR), (IntermediateField.inclusion h).comp τ', fun x => hI x, fun n => ?_⟩
  rw [hc n, hmult3, hmult]

end Local

end GlobalTheory.ConjCrys

open GlobalTheory.ConjCrys in

theorem GlobalTheory.crysWith_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (A : GL (Fin n) (PadicAlgCl l)) (K : FinExt l) (Jm : (E →+* PadicAlgCl l) → Multiset ℤ), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1 ∧ ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1) → CrysWith r Jm → CrysWith ((MulAut.conj A⁻¹).toMonoidHom.comp r) Jm := by
  intro E Ω _ _ _ _ _ l _ n r A K Jm hA hr
  obtain ⟨hcont, hloc⟩ := hr
  refine ⟨?_, fun P AI hT w B hB O _ _ _ Bw hInd => ?_⟩
  · change Continuous fun g => A⁻¹ * r g * A⁻¹⁻¹
    exact (continuous_const.mul hcont).mul continuous_const
  · obtain ⟨h1, h2⟩ := hloc P AI hT w B hB O Bw hInd
    have e : ((MulAut.conj A⁻¹).toMonoidHom.comp r).comp (Dec (F := E) B).subtype =
        (MulAut.conj A⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) B).subtype) := MonoidHom.comp_assoc _ _ _
    rw [e]
    refine ⟨isCrysAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA h1, fun τ LL' τ' hI => ?_⟩
    exact isJumpsAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA (h2 τ LL' τ' hI)
