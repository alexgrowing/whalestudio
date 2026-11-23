import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThListTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedFieldKerToPermFiniteIsGaloisFinrankDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThGOfPolFibField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThListConj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GalTh

theorem thList_galois : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ S) (θ : SecAt G L x), Odd m → N = m ^ (4 * g) → PolFib G L g x → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (pt : Fin N → (Over.mk (spMap (algebraMap Ω Ω') ≫ x) ⟶ G)) (c : Fin N → Ω'), FiniteDimensional Ω Ω' ∧ IsGalois Ω Ω' ∧ Module.finrank Ω Ω' ∣ N.factorial ∧ ThList G L ρ m (spMap (algebraMap Ω Ω') ≫ x) (SecAt.pull G L θ (algebraMap Ω Ω')) pt c ∧ ∀ τ : Ω' ≃ₐ[Ω] Ω', ∃ σ : Equiv.Perm (Fin N), ∀ a, τ (c a) = c (σ a) := by
  intro S G _ _ L ρ hL hρ g m N Ω _ _ x θ hm hN hP
  classical
  have hp : IsGrpPullback G G (𝟙 _) (𝟙 G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G) (inferInstanceAs (IsMonHom (𝟙 G)))
  have hid : LBIso L (L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl hL).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  have fibBase : ∀ {R R' : Type} [CommRing R] [CommRing R'] (y : Sp R ⟶ S) (i : R →+* R'),
      PolFib G L g y → PolFib G L g (spMap i ≫ y) := fun y i h =>
    (GlobalTheory.UMin.FibMove.polFib_move S S G L G L (𝟙 S) (𝟙 G.left) hL hL hp hid g _ y).2 _ i h
  let K := AlgebraicClosure Ω
  let ι₀ : Ω →+* K := algebraMap Ω K
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap Ω K).injective
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
  have hPK : PolFib G L g (spMap ι₀ ≫ x) := fibBase x ι₀ hP
  obtain ⟨ptK, cK, hK⟩ := GlobalTheory.UMin.exists_thList S G L ρ hL hρ g m N K (spMap ι₀ ≫ x) (SecAt.pull G L θ ι₀) hm hmK hN hPK
  obtain ⟨φ, hφ⟩ := GlobalTheory.UMin.GalConj.thList_conj S G L ρ hL hρ g m N Ω K x θ ptK cK hm hmK hPK hK
  obtain ⟨hfd, hgal, hdeg⟩ := GlobalTheory.fixedField_ker_toPerm_finite_isGalois_finrank_dvd Ω K N φ
  set Ω' := IntermediateField.fixedField φ.ker with hΩ'
  have hfix : ∀ a, ∀ τ ∈ φ.ker, spMap (τ : K →+* K) ≫ (ptK a).left = (ptK a).left := fun a τ hτ => by
    have h1 := (hφ τ a).1
    rwa [MonoidHom.mem_ker.1 hτ, Equiv.Perm.one_apply] at h1
  choose q hq using fun a => exists_descend φ.ker (ptK a).left (hfix a)
  let inc : Ω' →+* K := algebraMap Ω' K
  let j : Ω →+* Ω' := algebraMap Ω Ω'
  have hincj : inc.comp j = ι₀ := (IsScalarTower.algebraMap_eq Ω Ω' K).symm
  have hqo : ∀ a, q a ≫ G.hom = spMap j ≫ x := fun a => sp_cancel inc _ _ (by
    rw [← Category.assoc, hq a, Over.w (ptK a), ← Category.assoc, ← sp_comp, hincj]; rfl)
  let pt' : Fin N → (Over.mk (spMap j ≫ x) ⟶ G) := fun a => Over.homMk (q a) (hqo a)
  let u : Over.mk (spMap ι₀ ≫ x) ⟶ Over.mk (spMap j ≫ x) :=
    Over.homMk (spMap inc) (by
      show spMap inc ≫ spMap j ≫ x = spMap ι₀ ≫ x
      rw [← Category.assoc, ← sp_comp, hincj])
  have hu : ∀ a, u ≫ pt' a = ptK a := fun a => Over.OverMorphism.ext (by simp [u, pt', hq a])
  have hinj' : Function.Injective pt' := fun a b h => hK.1 (by rw [← hu a, ← hu b, h])
  have htor : ∀ a, pt' a ^ (m ^ 2) = 1 := fun a => by
    have e : u ≫ pt' a ^ (m ^ 2) = u ≫ 1 := by rw [MonObj.comp_pow, hu, (hK.2.1 a).1, MonObj.comp_one]
    have e2 := congrArg (fun f => f.left) e
    simp only [Over.comp_left] at e2
    exact Over.OverMorphism.ext (sp_cancel inc _ _ e2)
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  have hm' : (m : Ω') ≠ 0 := Nat.cast_ne_zero.2 hm0
  have hP' : PolFib G L g (spMap j ≫ x) := fibBase x j hP
  choose c' hc' using fun a => GlobalTheory.UMin.exists_thG_of_polFib_field S G L ρ hL hρ g m Ω' (spMap j ≫ x) (SecAt.pull G L θ j) (pt' a) hm hm' hP' (htor a)
  have hT : ThList G L ρ m (spMap j ≫ x) (SecAt.pull G L θ j) pt' c' := by
    refine ⟨hinj', hc', fun K'' _ _ i p hpm => ?_⟩
    have hm'' : (m : K'') ≠ 0 := by rw [← map_natCast i]; exact (map_ne_zero i).2 hm'
    obtain ⟨pt₂, c₂, h₂⟩ := GlobalTheory.UMin.exists_thList S G L ρ hL hρ g m N K'' (spMap i ≫ spMap j ≫ x)
      (SecAt.pull G L (SecAt.pull G L θ j) i) hm hm'' hN (fibBase _ i hP')
    let w : Over.mk (spMap i ≫ spMap j ≫ x) ⟶ Over.mk (spMap j ≫ x) := Over.homMk (spMap i) rfl
    have hv : ∀ a, ∃ b, w ≫ pt' a = pt₂ b := fun a =>
      thList_exh h₂ _ (by rw [← MonObj.comp_pow, htor, MonObj.comp_one])
    choose π hπ using hv
    have hπi : Function.Injective π := fun a b h => hinj' (Over.OverMorphism.ext (sp_cancel i _ _ (by
      have := congrArg (fun f => f.left) ((hπ a).trans ((congrArg pt₂ h).trans (hπ b).symm))
      simpa [w] using this)))
    obtain ⟨b, hb⟩ := thList_exh h₂ p hpm
    obtain ⟨a, rfl⟩ := (Finite.injective_iff_surjective.1 hπi) b
    refine ⟨a, ?_⟩
    rw [hb, ← hπ a]; rfl
  refine ⟨Ω', inferInstance, inferInstance, pt', c', hfd, hgal, hdeg, hT, fun τ => ?_⟩
  obtain ⟨pt'', -, h''⟩ := GlobalTheory.UMin.ThPull.thList_pull S G L ρ hL hρ m N Ω' K inc (spMap j ≫ x) (SecAt.pull G L θ j) pt' c' hT
  obtain ⟨pt₃, -, h₃⟩ := thList_comp m j inc ι₀ hincj x θ pt'' _ h''
  obtain ⟨φ', hφ'⟩ := GlobalTheory.UMin.GalConj.thList_conj S G L ρ hL hρ g m N Ω K x θ pt₃ _ hm hmK hPK h₃
  let τ' : K ≃ₐ[Ω] K := τ.liftNormal K
  refine ⟨φ' τ', fun b => ?_⟩
  apply inc.injective
  exact (AlgEquiv.liftNormal_commutes τ K (c' b)).symm.trans (hφ' τ' b).2

end GlobalTheory.UMin.GalTh
