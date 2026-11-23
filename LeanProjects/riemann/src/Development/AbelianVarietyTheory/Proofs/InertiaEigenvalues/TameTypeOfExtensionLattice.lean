import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TameExt

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions

theorem aeval_intertwine {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (a : Module.End R M) (b : Module.End R N) (hab : ∀ v, b (f v) = f (a v))
    (p : Polynomial R) (v : M) : Polynomial.aeval b p (f v) = f (Polynomial.aeval a p v) := by
  have hpow : ∀ (n : ℕ) v, (b ^ n) (f v) = f ((a ^ n) v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, hab, ih, pow_succ, Module.End.mul_apply]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, map_smul]

section Gen

variable {G H : Type} [Group G] [Group H] (ι : H →* G)
  {Qp K₀ K K₀' K' B BdR : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
  [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
  [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
  [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
  [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
  [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
  [Algebra K₀' B] [IsScalarTower Qp K₀' B]
  [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
  [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
  (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData H Qp K₀' K' B BdR)
  {LL : Type} [Field LL] [Algebra Qp LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem actVB_comp' (hι : ∀ h b, PD'.actB h b = PD.actB (ι h) b) (ρ : Representation LL G V) (h : H)
    (v : V ⊗[Qp] B) : actVB PD' (ρ.comp ι) h v = actVB PD ρ (ι h) v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    change ρ (ι h) v ⊗ₜ[Qp] PD'.actB h b = ρ (ι h) v ⊗ₜ[Qp] PD.actB (ι h) b
    rw [hι]

theorem actVB_mulVB' (ρ : Representation LL G V) (g : G) (k : K₀')
    (hk : PD.actB g (algebraMap K₀' B k) = algebraMap K₀' B k) (v : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (LL := LL) k v) = mulVB (LL := LL) k (actVB PD ρ g v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    change ρ g v ⊗ₜ[Qp] PD.actB g (algebraMap K₀' B k * b) = ρ g v ⊗ₜ[Qp] (algebraMap K₀' B k * PD.actB g b)
    rw [map_mul, hk]

theorem snd_actVB' (ρ : Representation LL H (V × LL)) (hρ : ∀ h v, (ρ h v).2 = v.2) (h : H)
    (w : (V × LL) ⊗[Qp] B) :
    AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (((PD'.actB h).toAlgHom.toLinearMap).restrictScalars Qp)
        (AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) w) =
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (actVB PD' ρ h w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul v b =>
    have h2 : LinearMap.snd LL V LL (ρ h v) = v.2 := hρ h v
    simp only [actVB, AlgebraTensorModule.map_tmul, AlgebraTensorModule.rTensor_tmul, h2]
    rfl

theorem aeval_extRep' [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [FiniteDimensional Qp LL]
    (hι : ∀ h b, PD'.actB h b = PD.actB (ι h) b) (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ))
    (hc : ∃ β : V ⊗[Qp] B, ∀ h, (c : G → V) h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h β - β)
    (g : G) (hg : ∀ k : K₀', PD.actB g (algebraMap K₀' B k) = algebraMap K₀' B k)
    (P : Polynomial LL) (hP : (Polynomial.X - Polynomial.C 1) ∣ P)
    (hTP : ∀ x ∈ Dcris PD' (ρ.comp ι), Polynomial.aeval (actVB PD ρ g : Module.End LL (V ⊗[Qp] B)) P x = 0)
    (x : (V × LL) ⊗[Qp] B) (hx : x ∈ Dcris PD' ((extRep ρ c).comp ι)) :
    Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B)) P x = 0 := by
  have hE := extRep_isExt ρ c
  obtain ⟨y, hy, hpy⟩ := (GlobalTheory.CrysExt.coboundary_iff_lift PD hE.1 hE.2).1 hc
  have hyfix : ∀ h : G, actVB PD (extRep ρ c) h y = y := (GlobalTheory.CrysSub.mem_Dcris _ _ _).1 hy
  have hf : ∀ (h : H) (v : V), LinearMap.inl LL V LL ((ρ.comp ι) h v) =
      ((extRep ρ c).comp ι) h (LinearMap.inl LL V LL v) := fun h v => hE.1.2.2.2.1 _ v
  have hq : ∀ (h : H) (v : V × LL), LinearMap.snd LL V LL (((extRep ρ c).comp ι) h v) =
      Representation.trivial LL H LL h (LinearMap.snd LL V LL v) := fun h v => hE.1.2.2.2.2 _ v
  have hkF : ∀ (h : H) (k : K₀'), PD.actB (ι h) (algebraMap K₀' B k) = algebraMap K₀' B k :=
    fun h k => (hι h _).symm.trans (AlgEquiv.commutes _ k)
  have hsm : ∀ (k : K₀') (v : (V × LL) ⊗[Qp] B),
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (mulVB (LL := LL) k v) =
        mulVB (LL := LL) k (AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) v) := by
    intro k v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVB]
    | add x y hx hy => simp only [map_add, hx, hy]

  have hlift1 : ∀ u : LL ⊗[Qp] K₀', ∃ x₁ : (V × LL) ⊗[Qp] B,
      x₁ ∈ Dcris PD' ((extRep ρ c).comp ι) ∧
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) x₁ = GlobalTheory.CrysExt.incl Qp K₀' B LL u ∧
      actVB PD (extRep ρ c) g x₁ = x₁ := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, zero_mem _, by simp, by simp⟩
    | tmul a k =>
      refine ⟨a • mulVB (LL := LL) k y, (GlobalTheory.CrysSub.mem_Dcris _ _ _).2 fun h => ?_, ?_, ?_⟩
      · rw [map_smul, actVB_comp' ι PD PD' hι, actVB_mulVB' PD _ _ k (hkF h k), hyfix]
      · rw [map_smul, hsm, hpy]
        simp [mulVB, smul_tmul']
      · rw [map_smul, actVB_mulVB' PD _ _ k (hg k), hyfix]
    | add u v hu hv =>
      obtain ⟨x₁, h1, h2, h3⟩ := hu
      obtain ⟨x₂, h4, h5, h6⟩ := hv
      exact ⟨x₁ + x₂, add_mem h1 h4, by rw [map_add, map_add, h2, h5], by rw [map_add, h3, h6]⟩

  obtain ⟨u, hu⟩ := (GlobalTheory.CrysExt.invariant_iff (fun h : H => PD'.actB h) PD'.invB _).1 fun h => by
    rw [snd_actVB' PD' ((extRep ρ c).comp ι) (fun h v => hE.1.2.2.2.2 (ι h) v) h x, (GlobalTheory.CrysSub.mem_Dcris _ _ _).1 hx h]
  obtain ⟨x₁, hx₁, hsx₁, hgx₁⟩ := hlift1 u

  have hD : x - x₁ ∈ Dcris PD' ((extRep ρ c).comp ι) := sub_mem hx hx₁
  have hker : (⟨x - x₁, hD⟩ : ↥(Dcris PD' ((extRep ρ c).comp ι))) ∈
      LinearMap.ker (GlobalTheory.CrysSub.Dmap PD' _ _ _ hq) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (x - x₁) = 0
    rw [map_sub, hsx₁, hu, sub_self]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.CrysSub.exact_Dmap PD' (ρ.comp ι) ((extRep ρ c).comp ι)
    (Representation.trivial LL H LL) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL)
    hf hq LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective hker
  have hx0 : AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL) (x₀ : V ⊗[Qp] B) = x - x₁ :=
    congrArg Subtype.val hx₀
  have hxe : x = x₁ + AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL) (x₀ : V ⊗[Qp] B) := by
    rw [hx0]; abel

  have hpart1 : Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B)) P x₁ = 0 := by
    obtain ⟨Q, rfl⟩ := hP
    rw [mul_comm, map_mul, Module.End.mul_apply]
    have h1 : Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B))
        (Polynomial.X - Polynomial.C (1 : LL)) x₁ = 0 := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_one, LinearMap.sub_apply, Module.End.one_apply,
        hgx₁, sub_self]
    rw [h1, map_zero]
  have hpart2 := aeval_intertwine (AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL))
    (actVB PD ρ g) (actVB PD (extRep ρ c) g)
    (fun v => (GlobalTheory.CrysSub.rTensor_act _ _ _ _ hE.1.2.2.2.1 g v).symm) P (x₀ : V ⊗[Qp] B)
  rw [hxe, map_add, hpart1, hpart2, hTP _ x₀.2, map_zero, add_zero]

end Gen

end GlobalTheory.TameExt

namespace GlobalTheory.TameExt

theorem tameType_extLat {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l}
    [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL) (Sig : Finset (ZMod e))
    (h0 : (0 : ZMod e) ∈ Sig) (hT : TameType a ϖ Pl T Sig) (z : ↥(latticeCocycles T.L))
    (hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ) :
    TameType a ϖ Pl (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) Sig := by
  intro g hg w hw x hx
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hP : (Polynomial.X - Polynomial.C (1 : ↥LL.1)) ∣ ∏ c ∈ Sig, (Polynomial.X - Polynomial.C (w ^ c.val)) := by
    have h1 := Finset.dvd_prod_of_mem (fun c : ZMod e => Polynomial.X - Polynomial.C (w ^ c.val)) h0
    rwa [ZMod.val_zero, pow_zero] at h1
  exact aeval_extRep' (inclG (ϖ.field a)) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (Pl.PD (ϖ.field a))
    (fun h b => (Pl.PD_actB _ h b).trans (Pl.PD_actB _ (inclG _ h) b).symm) T.ρ ⟨z, z.2.1⟩ hz.2 g
    (fun k => (Pl.PD_actB _ g _).trans (Pl.actQ_Kur _ ⟨k, k.2.2⟩ ⟨k, k.2.2⟩
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (GlobalTheory.BKGal.UnitModel.fix_Kur hg) _ k.2.2)))
    _ hP (hT g hg w hw) x hx

end GlobalTheory.TameExt
