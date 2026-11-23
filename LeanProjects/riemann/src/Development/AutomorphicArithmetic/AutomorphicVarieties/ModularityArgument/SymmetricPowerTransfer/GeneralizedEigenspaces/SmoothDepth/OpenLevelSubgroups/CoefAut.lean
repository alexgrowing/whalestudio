import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem exists_finPart {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} :
    ∃ p : UA L n → finU L n, Continuous p ∧ p 1 = 1 ∧ ∀ x, (p x : UA L n)⁻¹ * x ∈ infU L n := by
  have hfin : Continuous (finGL L n) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
      (continuous_const.prodMk continuous_id : Continuous fun x : Af L => ((0, x) : InfiniteAdeleRing L × Af L))))
  refine ⟨fun x => ⟨⟨finGL L n (Matrix.GeneralLinearGroup.map (pFin L) x.1),
    GlobalTheory.SplitPts.finGL_mem_UA _ fun u => GlobalTheory.SplitPts.comp_eq x u⟩, MonoidHom.mem_ker.2 (pInf_finGL _)⟩,
    Continuous.subtype_mk (Continuous.subtype_mk
      (hfin.comp (GlobalTheory.DefU.continuous_map_pFin.comp continuous_subtype_val)) _) _, ?_, fun x => ?_⟩
  · refine Subtype.ext (Subtype.ext ?_)
    change finGL L n (Matrix.GeneralLinearGroup.map (pFin L) 1) = 1
    rw [map_one, map_one]
  · change Matrix.GeneralLinearGroup.map (pFin L)
      ((finGL L n (Matrix.GeneralLinearGroup.map (pFin L) x.1))⁻¹ * x.1) = 1
    rw [map_mul, map_inv, pFin_finGL, inv_mul_cancel]

private theorem continuous_infC {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} :
    Continuous (infC L n) := by
  have hτ : ∀ τ : L →+* ℂ, Continuous (cEmb (E := L) (n := n) τ) := fun τ => by
    have h1 : Continuous (coord (E := L) τ) := by
      unfold coord
      split_ifs
      · exact continuous_apply _
      · exact Complex.continuous_conj.comp (continuous_apply _)
    have h2 : Continuous (pInf L) := continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst)
    exact (Continuous.units_map _ (continuous_id.matrix_map h1)).comp
      ((Continuous.units_map _ (continuous_id.matrix_map h2)).comp continuous_subtype_val)
  exact continuous_pi fun v => hτ v.embedding

private theorem infC_of_fin {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {k : UA L n}
    (hk : k ∈ finU L n) : infC L n k = 1 :=
  funext fun v => by
    change Matrix.GeneralLinearGroup.map (coord v.embedding) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]

theorem UpperTheory.V.Z.Sym.Al.coefAut :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U → ∀ φ : UA L n → V, IsAF R U φ →
        ∀ f : V →ₗ[ℂ] ℂ, IsAutFormU (f ∘ φ) := by
  intro L _ _ _ n V _ _ _ R hR U hU φ hφ f
  obtain ⟨p, hp, hp1, hp2⟩ := exists_finPart (L := L) (n := n)
  have hU1 : {x : finU L n | (x : UA L n) ∈ U} ∈ nhds (1 : finU L n) := hU.2.mem_nhds U.one_mem

  have hsm : ∀ᶠ z in nhds (1 : UA L n), ∀ g, φ (g * z) = R (infC L n z⁻¹) (φ g) := by
    have hUp : {x : finU L n | (x : UA L n) ∈ U} ∈ nhds (p 1) := by rwa [hp1]
    filter_upwards [(hp.tendsto 1).eventually hUp] with z hz g
    have h1 := hφ.inf _ (hp2 z) (g * (p z : UA L n))
    rw [hφ.level _ hz g, mul_assoc, mul_inv_cancel_left] at h1
    have e : infC L n ((p z : UA L n)⁻¹ * z)⁻¹ = infC L n z⁻¹ := by
      rw [mul_inv_rev, inv_inv, map_mul, infC_of_fin (p z).2, mul_one]
    rw [h1, e]
  refine ⟨?_, fun γ hγ g => congrArg f (hφ.left γ hγ g), ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA L n => f (R (infC L n (g⁻¹ * g0)) (φ g0)) :=
      (hR (φ g0) f).comp (continuous_infC.comp (continuous_inv.mul continuous_const))
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA L n => g0⁻¹ * g) (nhds g0) (nhds 1) := by
      have : Continuous fun g : UA L n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left, mul_inv_rev, inv_inv] at e
    rw [Function.comp_apply, e]
  · refine isOpen_stab_of_mem_nhds ((RU L n).comp (finU L n).subtype) _ ?_
    filter_upwards [hU1] with k hk
    funext g
    exact congrArg f (hφ.level _ hk g)
  · let C : Module.Dual ℂ V →ₗ[ℂ] (UA L n → ℂ) :=
      { toFun := fun μ g => μ (φ g)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range C) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨f ∘ₗ R (infC L n (k : UA L n)⁻¹), ?_⟩
    funext g
    change f (R (infC L n (k : UA L n)⁻¹) (φ g)) = f (φ (g * k))
    rw [hφ.inf _ k.2 g]
