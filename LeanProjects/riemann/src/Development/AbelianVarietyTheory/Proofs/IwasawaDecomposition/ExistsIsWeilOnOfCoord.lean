import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumEqTraceOriented
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilTransport

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem integral_transport {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y] [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (E : X ≃+ Y) (hc : Continuous E) (hc' : Continuous E.symm) (LX : AddSubgroup X) (LY : AddSubgroup Y)
    (hL : ∀ x, x ∈ LX ↔ E x ∈ LY) {f g : Y → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ (μ : Measure X) (𝓕 : Set X), μ.IsAddHaarMeasure → IsAddFundamentalDomain LX 𝓕 μ →
      ∫⁻ w in 𝓕, ‖f (E w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖g (E w)‖ₑ ^ 2 ∂μ)
    (μ : Measure Y) (𝓕 : Set Y) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain LY 𝓕 μ) :
    ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖g w‖ ^ 2 ∂μ := by
  let M : X ≃ᵐ Y := (⟨E.toEquiv, hc, hc'⟩ : X ≃ₜ Y).toMeasurableEquiv
  have hM : MeasurePreserving M (μ.map E.symm) μ :=
    (⟨M.symm.measurable, rfl⟩ : MeasurePreserving M.symm μ (μ.map E.symm)).symm M.symm
  have h1 : (μ.map E.symm).IsAddHaarMeasure := E.symm.isAddHaarMeasure_map μ hc' hc
  have h2 : IsAddFundamentalDomain LX (M ⁻¹' 𝓕) (μ.map E.symm) := by
    refine h𝓕.preimage_of_equiv hM.quasiMeasurePreserving
      (e := fun y : LY => (⟨E.symm y, (hL _).2 (by simp)⟩ : LX)) ⟨fun a b hab => ?_, fun x => ?_⟩ fun y x => ?_
    · exact Subtype.ext (E.symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨E x, (hL _).1 x.2⟩, Subtype.ext (E.symm_apply_apply _)⟩
    · show E (E.symm y + x) = y + E x
      simp
  have key : ∀ k : Y → ℂ, Continuous k →
      ∫ w in 𝓕, ‖k w‖ ^ 2 ∂μ = (∫⁻ w in M ⁻¹' 𝓕, ‖k (E w)‖ₑ ^ 2 ∂(μ.map E.symm)).toReal := fun k hk => by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖k w‖ ^ 2) (Filter.Eventually.of_forall fun w => by positivity)
      (hk.norm.pow 2).measurable.aestronglyMeasurable]
    congr 1
    rw [← hM.setLIntegral_comp_preimage_emb M.measurableEmbedding (fun w => ENNReal.ofReal (‖k w‖ ^ 2)) 𝓕]
    refine lintegral_congr fun w => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl
  rw [key f hf, key g hg, h _ _ h1 h2]

structure IsCoord (S T V W : HSp D) (E : WO S T ≃+ WA V W) : Prop where
  cont : Continuous E
  cont' : Continuous E.symm
  sympl : ∀ x y, symplOH S T x y = symplH V W (E x) (E y)
  rat : ∀ x, x ∈ ratL T S ↔ E x ∈ ratL V W
  inf : ∀ x : WO S T, x.map (infPart D) = 0 ↔ (E x).map (infPart D) = 0
  fin : ∀ x : WO S T, x.map (finPart D) = 0 ↔ (E x).map (finPart D) = 0
  part : ∀ (a : AE D) (x : WO S T), (∀ i j, a * x i j = x i j) → ∀ i j, a * E x i j = E x i j

namespace IsCoord

variable {S T V W : HSp D} {E : WO S T ≃+ WA V W} (hE : IsCoord S T V W E) (ψ : AddChar (AF D.host.F) ℂ)

include hE

theorem heis_comp (u : WO S T) (f : WA V W → ℂ) : Heisenberg₂ ψ V W (E u) f ∘ E = heisO ψ S T u (f ∘ E) := by
  funext w
  simp only [Function.comp_apply, Heisenberg₂, heisO, hE.sympl, map_add]

theorem theta_iff (f : WA V W → ℂ) : IsThetaFunO ψ S T (f ∘ E) ↔ IsThetaFun ψ V W f := by
  constructor
  · intro hf
    refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
    · obtain ⟨δ, hδ⟩ := (hE.rat (E.symm (ratW V W γ))).2 (by rw [E.apply_symm_apply]; exact ⟨γ, rfl⟩)
      have hδ' : ratW T S δ = E.symm (ratW V W γ) := hδ
      have := hf.quasi δ (E.symm w)
      simpa only [hδ', Function.comp_apply, map_add, hE.sympl, E.apply_symm_apply] using this
    · obtain ⟨U, hU, hfix⟩ := hf.level
      refine ⟨U.comap E.symm.toAddMonoidHom, hU.preimage hE.cont', fun u hu h0 => ?_⟩
      have := hfix (E.symm u) hu ((hE.inf _).2 (by rwa [E.apply_symm_apply]))
      rw [← hE.heis_comp, E.apply_symm_apply] at this
      exact E.surjective.injective_comp_right this
    · have := hf.cont.comp hE.cont'
      simpa only [Function.comp_def, E.apply_symm_apply] using this
    · have := hf.smooth k (E.symm.toAddMonoidHom.comp L) (hE.cont'.comp hL)
        (fun t => (hE.fin _).2 (by simpa using h0 t)) (E.symm w)
      simpa using this
  · intro hf
    refine ⟨fun γ w => ?_, ?_, hf.cont.comp hE.cont, fun k L hL h0 w => ?_⟩
    · obtain ⟨δ, hδ⟩ := (hE.rat (ratW T S γ)).1 ⟨γ, rfl⟩
      have hδ' : ratW V W δ = E (ratW T S γ) := hδ
      have := hf.quasi δ (E w)
      simpa only [hδ', Function.comp_apply, map_add, hE.sympl] using this
    · obtain ⟨U, hU, hfix⟩ := hf.level
      refine ⟨U.comap E.toAddMonoidHom, hU.preimage hE.cont, fun u hu h0 => ?_⟩
      rw [← hE.heis_comp, hfix (E u) hu ((hE.inf _).1 h0)]
    · have := hf.smooth k (E.toAddMonoidHom.comp L) (hE.cont.comp hL) (fun t => (hE.fin _).1 (h0 t)) (E w)
      simpa using this

end IsCoord

theorem exists_isWeilOn_of_coord {S T V W : HSp D} {E : WO S T ≃+ WA V W} (hE : IsCoord S T V W E)
    {ψ : AddChar (AF D.host.F) ℂ} {χS χT χ χ' : IdC D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (j : GA D V × GA D W →* GA D S × GA D T) (hj : Continuous j)
    (hact : ∀ g h x, E (actO S T (j (g, h)).1 (j (g, h)).2 x) = actHom V W g h (E x))
    (hrat : ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, (j (γ, γ')).1 ∈ GQ S ∧ (j (γ, γ')).2 ∈ GQ T)
    (hsp : ∀ e g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
      ∃ x' y', SuppAt e S (j (g, h)).1 ∧ SuppAt e T (j (g, h)).2 ∧ IsDetAt e S (j (g, h)).1 x' ∧
        IsDetAt e T (j (g, h)).2 y' ∧ splitFacO χS χT x' y' = splitFac V W χ χ' x y) :
    ∃ om', IsWeilOn ψ V W χ χ' om' := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  let P : (WA V W → ℂ) ≃ₗ[ℂ] (WO S T → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ E.toEquiv
  have hP : ∀ f, P f = f ∘ E := fun _ => rfl
  have hPs : ∀ f, P.symm f ∘ E = f := fun f => P.apply_symm_apply f
  have th : ∀ Φ : ThS ψ V W, IsThetaFunO ψ S T (Φ.1 ∘ E) := fun Φ => (hE.theta_iff ψ _).2 (mem_ThS.1 Φ.2)
  have th' : ∀ f, IsThetaFunO ψ S T f → P.symm f ∈ ThS ψ V W := fun f hf =>
    mem_ThS.2 ((hE.theta_iff ψ _).1 (by rwa [hPs]))
  have pres : ∀ p, ∀ f ∈ ThS ψ V W, P.symm.conj (om (j p)) f ∈ ThS ψ V W := fun p f hf =>
    th' _ (H.om_pres _ _ (th ⟨f, hf⟩))
  let om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W) :=
    { toFun := fun p => (P.symm.conj (om (j p))).restrict (pres p)
      map_one' := LinearMap.ext fun Φ => Subtype.ext (by
        show P.symm (om (j 1) (P Φ.1)) = Φ.1
        rw [map_one, map_one, Module.End.one_apply, P.symm_apply_apply])
      map_mul' := fun p q => LinearMap.ext fun Φ => Subtype.ext (by
        show P.symm (om (j (p * q)) (P Φ.1)) = P.symm (om (j p) (P (P.symm (om (j q) (P Φ.1)))))
        rw [map_mul, map_mul, Module.End.mul_apply, P.apply_symm_apply]) }
  have ho : ∀ p (Φ : ThS ψ V W), (om' p Φ).1 ∘ E = om (j p) (Φ.1 ∘ E) := fun p Φ => hPs _
  refine ⟨om', fun g h w₀ Φ Φ' e => ?_, fun γ hγ γ' hγ' Φ => ?_, fun Φ w => ?_, fun μ 𝓕 hμ h𝓕 p Φ => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩
  · obtain ⟨u, rfl⟩ := E.surjective w₀
    refine E.surjective.injective_comp_right ?_
    show (om' (g, h) Φ').1 ∘ E = Heisenberg₂ ψ V W (actHom V W g h (E u)) (om' (g, h) Φ).1 ∘ E
    rw [← hact, hE.heis_comp, ho, ho, e, hE.heis_comp]
    exact H.om_heis _ _ u _ (th Φ)
  · have h1 := congrFun (ho (γ, γ') Φ) 0
    have h2 := H.om_aut _ (hrat γ hγ γ' hγ').1 _ (hrat γ hγ γ' hγ').2 _ (th Φ)
    have h3 := h1.trans h2
    simpa only [Function.comp_apply, map_zero] using h3
  · obtain ⟨u, rfl⟩ := E.surjective w
    exact ((H.om_cont _ (th Φ) u).comp hj).congr fun p => (congrFun (ho p Φ) u).symm
  · refine @integral_transport (WO S T) (WA V W) _ _ _ _ _ _ (borel _) (borel _) (@BorelSpace.mk _ _ (borel _) rfl)
      (@BorelSpace.mk _ _ (borel _) rfl) E hE.cont hE.cont' (ratL T S) (ratL V W) hE.rat _ _
      (mem_ThS.1 (om' p Φ).2).cont (mem_ThS.1 Φ.2).cont (fun ν 𝓖 hν h𝓖 => ?_) μ 𝓕 hμ h𝓕
    have := H.om_unit ν 𝓖 hν h𝓖 (j p) _ (th Φ)
    rw [← ho] at this
    exact this
  · obtain ⟨x', y', k1, k2, k3, k4, k5⟩ := hsp e g h hg hh x y hx hy
    obtain ⟨r, hr, hℓ⟩ := H.om_split e he _ _ k1 k2 x' y' k3 k4
    refine ⟨r, hr, fun ℓ hinv Φ => ?_⟩
    obtain ⟨L, hL⟩ := LinearMap.exists_extend ℓ
    have hL' : ∀ Ψ : ThS ψ V W, L Ψ.1 = ℓ Ψ := fun Ψ => LinearMap.congr_fun hL Ψ
    have key := hℓ (L ∘ₗ P.symm.toLinearMap) (fun u hu f hf => ?_) _ (th Φ)
    · rw [k5] at key
      have e1 : L (P.symm (Φ.1 ∘ E)) = ℓ Φ := by rw [← hP, P.symm_apply_apply, hL']
      rw [← hL', ← e1]
      exact key
    · have e2 : P.symm (heisO ψ S T u f) = Heisenberg₂ ψ V W (E u) (P.symm f) := by
        rw [LinearEquiv.symm_apply_eq, hP, hE.heis_comp, hPs]
      have m1 := th' f hf
      have m2 : Heisenberg₂ ψ V W (E u) (P.symm f) ∈ ThS ψ V W :=
        mem_ThS.2 (GlobalTheory.Mem.ThetaClosed.isThetaFun_heis H.std (mem_ThS.1 m1) _)
      show L (P.symm (heisO ψ S T u f)) = L (P.symm f)
      rw [e2]
      exact (hL' ⟨_, m2⟩).trans ((hinv (E u) (hE.part _ u hu) ⟨_, m1⟩ ⟨_, m2⟩ rfl).trans (hL' ⟨_, m1⟩).symm)

theorem gram_mul_gramInv (V : HSp D) : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedSmall.gramInv_mul V)

def mulGramInv (S T : HSp D) : WO S T ≃+ WA T S where
  toFun x := HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) ((S.gram⁻¹).map (incA D))
  invFun x := HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (S.gram.map (incA D))
  left_inv x := by
    show x * _ * _ = x
    rw [Matrix.mul_assoc, GlobalTheory.OrientedSmall.gramInv_mul, Matrix.mul_one]
  right_inv x := by
    show x * _ * _ = x
    rw [Matrix.mul_assoc, gram_mul_gramInv, Matrix.mul_one]
  map_add' x y := Matrix.add_mul _ _ _

theorem map_mulGramInv {R : Type} [CommRing R] (φ : AE D →+* R) (S T : HSp D) (x : WO S T) :
    x.map φ = 0 ↔ (mulGramInv S T x).map φ = 0 := by
  constructor
  · intro h
    exact (Matrix.map_mul (f := φ)).trans (by rw [h, Matrix.zero_mul])
  · intro h
    rw [← (mulGramInv S T).symm_apply_apply x]
    exact (Matrix.map_mul (f := φ)).trans (by rw [h, Matrix.zero_mul])

theorem isCoord_large (S T : HSp D) (hr : S.rank < T.rank) : IsCoord S T T S (mulGramInv S T) where
  cont := continuous_id.matrix_mul continuous_const
  cont' := continuous_id.matrix_mul continuous_const
  sympl x y := by
    rw [← GlobalTheory.WeilTieCheck.symplH_transpose T S hr.ne']
    unfold symplOH symplH
    rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr.le).1]
    rfl
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨γ * S.gram⁻¹, Matrix.map_mul (f := incA D)⟩
    · rintro ⟨γ, hγ⟩
      refine ⟨γ * S.gram, (Matrix.map_mul (f := incA D)).trans ?_⟩
      rw [← (mulGramInv S T).symm_apply_apply x, ← hγ]
      rfl
  inf := map_mulGramInv _ S T
  fin := map_mulGramInv _ S T
  part a x h i j := by
    show a * ∑ k, x i k * incA D (S.gram⁻¹ k j) = ∑ k, x i k * incA D (S.gram⁻¹ k j)
    simp only [Finset.mul_sum, ← mul_assoc, h]

theorem isCoord_small (S T : HSp D) (hr : S.rank < T.rank) :
    IsCoord S T S T ((mulGramInv S T).trans (Matrix.transposeAddEquiv _ _ _)) where
  cont := (isCoord_large S T hr).cont.matrix_transpose
  cont' := (isCoord_large S T hr).cont'.comp continuous_id.matrix_transpose
  sympl x y := ((isCoord_large S T hr).sympl x y).trans (GlobalTheory.WeilTieCheck.symplH_transpose T S hr.ne' _ _).symm
  rat x := ((isCoord_large S T hr).rat x).trans
    ⟨fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩, fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩⟩
  inf x := ((isCoord_large S T hr).inf x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  fin x := ((isCoord_large S T hr).fin x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  part a x h i j := (isCoord_large S T hr).part a x h j i

theorem weilCoreEx_of_datum : ∀ D : D7, (∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : IdC D), IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT om) → WeilCoreEx D := by
  intro D hO ψ hψ
  have key : ∀ (V W : HSp D) (χ χ' : IdC D), ∃ om, admitted V W χ χ' → IsWeilOn ψ V W χ χ' om := by
    intro V W χ χ'
    by_cases ha : admitted V W χ χ'
    swap
    · exact ⟨1, fun h => absurd h ha⟩
    obtain ⟨hne, h1, h2, h3, h4⟩ := ha
    suffices h : ∃ om, IsWeilOn ψ V W χ χ' om from h.imp fun _ h _ => h
    rcases lt_or_gt_of_ne hne with hr | hr
    · obtain ⟨om, H⟩ := hO ψ hψ V W χ χ' h1.1 h2.1 h3 h4
      refine exists_isWeilOn_of_coord (isCoord_small V W hr) H (MonoidHom.id _) continuous_id
        (fun g h x => (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x) (fun _ a _ b => ⟨a, b⟩)
        fun e g h hg hh x y hx hy => ⟨x, y, hg, hh, hx, hy, ?_⟩
      unfold splitFacO splitFac
      rw [if_pos hr.le]
    · obtain ⟨om, H⟩ := hO ψ hψ W V χ' χ h2.1 h1.1 h4 h3
      refine exists_isWeilOn_of_coord (isCoord_large W V hr) H ((MonoidHom.snd _ _).prod (MonoidHom.fst _ _)) continuous_swap
        (fun g h x => ?_) (fun _ a _ b => ⟨b, a⟩) fun e g h hg hh x y hx hy => ⟨y, x, hh, hg, hy, hx, ?_⟩
      · have e1 := (GlobalTheory.OrientedSmall.bridgeSmall D W V hr.le).2 h g x
        have e2 := actHom_swap V W hne g h (mulGramInv W V x)
        exact Matrix.transpose_injective (e1.trans e2)
      · unfold splitFacO splitFac
        rw [if_neg (not_le.2 hr), mul_comm]
  choose om hom using key
  exact ⟨⟨om, hom⟩⟩

end GlobalTheory.Mem.WeilTransport

end
