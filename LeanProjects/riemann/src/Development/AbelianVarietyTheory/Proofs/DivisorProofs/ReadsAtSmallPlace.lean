import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualWeylTensorLiftCoefficientSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorLiftEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPhiOfFrameInjectiveShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalisedStandardWeylOfLiftMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularMatricesPreserveFrameLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisIntegralRelativeAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPointIntegralRelativeLocalBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisDualBasisEmbeddedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntermediateFieldPadicIntegersEqNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneIffIntegralAtPadicEmbeddingPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEqOneOfIsLocEnv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

open Formalism.IndefR.Bridge

theorem avatar_comm {C W M I : Type} [Field C] [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module C M] (io : C ≃+* ℂ)
    (θ : W →+ M) (hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w) (A : Module.End ℂ W) (B : Module.End C M) (v : I → W)
    (hv : Submodule.span ℂ (Set.range v) = ⊤) (h : ∀ i, θ (A (v i)) = B (θ (v i))) (x : W) : θ (A x) = B (θ x) := by
  have hx : x ∈ Submodule.span ℂ (Set.range v) := hv ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h i
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hs, hx]

theorem exists_reading_lat {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {T : Type} [Fintype T]
    [DecidableEq T] {n : ℕ} {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)
    (lab : T → (E →+* K)) (lam : T → DomWeight n) (c0 : VV K lam →ₛₗ[σ] W) (e : S.V ≃ₗ[K] VV K lam) (hce : ∀ x, P.coef x = c0 (e x))
    (Lat : S.Cl → Submodule (𝓞 E) (Fin n → E)) (hlat : ∀ c, Submodule.IsLattice E (Lat c))
    (hN : ∀ c, (S.Nab c).map ((e : S.V →ₗ[K] VV K lam).restrictScalars (𝓞 K)) = nabAtr lab lam (Lat c))
    (hD : ∀ c, (S.Del c).map ((e : S.V →ₗ[K] VV K lam).restrictScalars (𝓞 K)) = delAtr lab lam (Lat c))
    (hc1 : LinearIndependent ℂ (fun i => c0 (bVV K lam i))) (hc2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤)
    {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (io : PadicAlgCl l ≃+* ℂ) (hw : AtPlace w e0)
    (hio : ∀ x, io (e0 x) = σ x) (m : G →* (T → GL (Fin n) (PadicAlgCl l)))
    (hrat : ∀ γ, ∃ γE, (∀ v, c0 (rhoVr lab lam γE v) = ρ γ (c0 v)) ∧
      m (ι γ) = fun τ => Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) γE)
    (hint : ∀ c B, Formalism.L2.Forms.IsLocBasis l (Lat c : Set (Fin n → E)) B → ∀ τ a b,
      ‖((m (P.y c) τ)⁻¹ * Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B).val a b‖ ≤ 1 ∧
      ‖((Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B)⁻¹ * m (P.y c) τ).val a b‖ ≤ 1)
    (lamW : T → ℕ → ℕ) (cs : T → ℤ) (hS : Shift lam lamW cs)
    (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) (hL : ∀ x, e0 x ∈ Lf) (hmL : ∀ g τ a b, (m g τ).val a b ∈ Lf) (F : Frame l T n)
    (hinj : Function.Injective F.emb) (hF : ∀ x, x ∈ Set.range F.emb ↔ x ∈ Lf ∧ ‖x‖ ≤ 1)
    (hk : ∀ (k : J) τ a b, (m k τ).val a b ∈ Set.range F.emb) (hχ : ∀ k : J, io.symm (χ k : ℂ) ∈ Set.range F.emb) :
    ∃ rd : S.Forms →ₛₗ[e0] (G → NablaT (PadicAlgCl l) n lamW),
      (∀ f γ g, rd f (ι γ * g) = rd f g) ∧
      (∀ f (k : J) g, lamG (PadicAlgCl l) n lamW cs (m k) (rd f (g * k)) = io.symm (χ k : ℂ) • rd f g) ∧
      (∀ (n : ℕ) (f : Fin n → S.Forms), LinearIndependent K f → LinearIndependent (PadicAlgCl l) fun a => rd (f a)) ∧
      (∀ (f f' : S.Forms) (A : Finset G), P.ext f' = dcOp A (P.ext f) → (∀ a ∈ A, m a = 1) →
        ∀ g, rd f' g = ∑ s ∈ A, rd f (g * s)) ∧
      (∀ f : S.Forms, (∀ c, (f : S.Cl → S.V) c ∈ S.Nab c) → ∀ g, rd f g ∈ F.latN lamW) ∧
      ∀ f : S.Forms, (∀ g, rd f g ∈ F.latD lamW) → ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∀ c, s • (f : S.Cl → S.V) c ∈ S.Del c := by
  obtain ⟨Φ, hΦ, hli⟩ := GlobalTheory.T.exists_dualWeylTensor_lift_coefficientSpace _ _ e0 _ _ lam lamW cs hS
  obtain ⟨θ, hs, hθ, hθi⟩ := exists_avatar io hio (bVV K lam) c0 hc1 hc2 Φ hli
  have heq := GlobalTheory.T.dualWeylTensorLift_equivariant _ _ e0 _ _ lam lamW cs Φ hS hΦ
  let Λ0 := lamG (PadicAlgCl l) n lamW cs
  let Λ : G →* Module.End (PadicAlgCl l) (NablaT (PadicAlgCl l) n lamW) := Λ0.comp m
  have hΛ : ∀ γ x, θ (ρ γ x) = Λ (ι γ) (θ x) := by
    intro γ x
    obtain ⟨γE, hγ, hE⟩ := hrat γ
    refine avatar_comm io θ hs _ _ _ hc2 (fun i => ?_) x
    rw [← hγ, hθ, hθ]
    refine (heq (embGL lab γE) _).trans ?_
    show Λ0 _ _ = Λ0 (m (ι γ)) _
    rw [hE]
    rfl
  obtain ⟨rd, h1, h2, h3, h4, h5⟩ := exists_reading P io hio θ hs hθi Λ hΛ
  have hanti : ∀ τ, Antitone (res n (lamW τ)) := fun τ a b hab => by
    have := (lam τ).anti hab
    have ha := hS τ a
    have hb := hS τ b
    show lamW τ b ≤ lamW τ a
    omega
  have hstab := GlobalTheory.T.unimodular_matrices_preserve_frame_lattices l _ n lamW cs F hinj hanti
  have hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by
    rw [hw]
    have : e0 (((l : ℕ) : 𝓞 K) : K) = algebraMap ℚ_[l] (PadicAlgCl l) l := by simp
    rw [this, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hmulL : ∀ A B : GL (Fin n) (PadicAlgCl l), (∀ a b, A.val a b ∈ Lf) → (∀ a b, B.val a b ∈ Lf) →
      ∀ a b, (A * B).val a b ∈ Lf := fun A B hA hB a b => by
    rw [Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun x _ => mul_mem (hA _ _) (hB _ _)

  have key : ∀ (c : S.Cl), ∃ (B : T → GL (Fin n) K) (u : T → GL (Fin n) (PadicAlgCl l)),
      (∀ τ, Submodule.IsLattice K (dualFr (tauLat lab τ (Lat c)))) ∧
      (∀ τ, IsBasisAt w (dualFr (tauLat lab τ (Lat c))) (B τ)) ∧
      (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) ∧
      ∀ v, Λ (P.y c)⁻¹ (Φ v) = Λ0 u (Φ (rhoK lam B⁻¹ v)) := by
    intro c
    have hb := fun τ => GlobalTheory.T.localBasis_dualBasis_embeddedLattice _ _ _ _ lab τ w l Fact.out hlw _ (hlat c)
    rcases isEmpty_or_nonempty T with hE | ⟨⟨τ0⟩⟩
    · refine ⟨1, 1, fun τ => hE.elim τ, fun τ => hE.elim τ, fun τ => hE.elim τ, fun v => ?_⟩
      have : m (P.y c)⁻¹ = 1 := Subsingleton.elim _ _
      show Λ0 (m (P.y c)⁻¹) _ = _
      rw [this, inv_one, map_one (rhoK lam)]
      rfl
    obtain ⟨B, hB⟩ := (hb τ0).1
    refine ⟨invTrK (embGL lab B), (m (P.y c))⁻¹ * fun τ => Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B,
      fun τ => (hb τ).2.1, fun τ => (hb τ).2.2 B hB, fun τ a b => ⟨(hF _).2 ⟨?_, ?_⟩, (hF _).2 ⟨?_, ?_⟩⟩, fun v => ?_⟩
    · refine hmulL _ _ (fun a b => ?_) (fun a b => hL _) a b
      rw [← map_inv]
      exact hmL _ τ a b
    · exact (hint c B hB τ a b).1
    · rw [Pi.mul_apply, mul_inv_rev, Pi.inv_apply, inv_inv, ← map_inv]
      exact hmulL _ _ (fun a b => hL _) (hmL _ τ) a b
    · rw [Pi.mul_apply, mul_inv_rev, Pi.inv_apply, inv_inv]
      exact (hint c B hB τ a b).2
    · rw [← map_inv invTrK, ← map_inv (embGL lab), heq]
      show Λ0 (m (P.y c)⁻¹) _ = (Λ0 _ * Λ0 _) _
      rw [← map_mul Λ0, map_inv m, mul_assoc]
      have : ((fun τ => Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B) *
          fun τ => Matrix.GeneralLinearGroup.map e0 (embGL lab B⁻¹ τ)) = 1 := by
        funext τ
        show Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B * Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B⁻¹ = 1
        rw [← map_mul, mul_inv_cancel, map_one]
      rw [this, mul_one]
  have hrange : ∀ x : K, ‖e0 x‖ ≤ 1 → e0 x ∈ Set.range F.emb := fun x hx => (hF _).2 ⟨hL x, hx⟩
  refine ⟨rd, h1, h2, h3, fun f f' A hA hA1 => h4 f f' A hA fun a ha => ?_, fun f hf g => ?_, fun f hf => ?_⟩
  · show Λ0 (m a) = 1
    rw [hA1 a ha, map_one]
  · have hy : ∀ c, rd f (P.y c) ∈ F.latN lamW := fun c => by
      obtain ⟨B, u, -, hB, hu, hv⟩ := key c
      rw [h5, hce, hθ, hv]
      refine (hstab u hu _).1 (GlobalTheory.T.isPhi_mem_latN_of_frame_injective_shift _ l w e0 _ _ lam lamW _ F Φ hw hinj hrange hS hΦ _ ?_)
      have hm : e ((f : S.Cl → S.V) c) ∈ nabAtr lab lam (Lat c) := hN c ▸ ⟨_, hf c, rfl⟩
      have hm' : ((e ((f : S.Cl → S.V) c) : VV K lam) : Pol K T n) ∈
        transLat lam (nabStd K lam) (fun τ => dualFr (tauLat lab τ (Lat c))) := hm
      simp only [transLat, Submodule.mem_iInf] at hm'
      exact hm' w B hB
    rw [P.dec_spec g, mul_assoc, h1]
    have h6 := congrArg (Λ0 (m (P.decK g)⁻¹)) (h2 f (P.decK g) (P.y (P.decC g)))
    have h7 : ∀ z, Λ0 (m (P.decK g)⁻¹) (Λ (P.decK g) z) = z := fun z => by
      show (Λ _ * Λ _) z = z
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [h7] at h6
    rw [h6]
    refine (hstab _ (fun τ a b => ⟨hk (P.decK g)⁻¹ τ a b, ?_⟩) _).1 ?_
    · rw [Subgroup.coe_inv, map_inv, Pi.inv_apply, inv_inv]
      exact hk _ τ a b
    · obtain ⟨r, hr⟩ := hχ (P.decK g)
      obtain ⟨x, hx⟩ := (GlobalTheory.LatBC.latN_iff F lamW _).1 (hy (P.decC g))
      exact (GlobalTheory.LatBC.latN_iff F lamW _).2 ⟨r • x, by rw [map_smulₛₗ, hr, hx]⟩
  · have hy : ∀ c, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • (f : S.Cl → S.V) c ∈ S.Del c := fun c => by
      obtain ⟨B, u, hlat', hB, hu, hv⟩ := key c
      have h6 := hf (P.y c)
      rw [h5, hce, hθ, hv] at h6
      have h7 := (hstab u⁻¹ (fun τ a b => ⟨(hu τ a b).2, by rw [Pi.inv_apply, inv_inv]; exact (hu τ a b).1⟩) _).2 h6
      have h8 : ∀ z, Λ0 u⁻¹ (Λ0 u z) = z := fun z => by
        show (Λ0 _ * Λ0 _) z = z
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [h8] at h7
      have h9 := GlobalTheory.T.mem_localisedStandardWeyl_of_lift_mem _ l w e0 _ _ lam lamW _ F Φ hw (fun x => ((hF _).1 ⟨x, rfl⟩).2) hS hΦ _ h7
      have h10 : ((e ((f : S.Cl → S.V) c) : VV K lam) : Pol K T n) ∈
          Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delP lam fun τ => dualFr (tauLat lab τ (Lat c))) := by
        rw [(GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 _ _ _ lam _ hlat' w B hB).2]
        refine ⟨_, h9, ?_⟩
        show (rhoP lam B * rhoP lam B⁻¹) _ = _
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl
      obtain ⟨s, hs1, hs2⟩ := h10
      refine ⟨s, hs1, ?_⟩
      have h11 : s • e ((f : S.Cl → S.V) c) ∈ delAtr lab lam (Lat c) := hs2
      rw [← hD c] at h11
      obtain ⟨x, hx, hxe⟩ := h11
      have : x = s • (f : S.Cl → S.V) c := e.injective (by
        rw [← algebraMap_smul K s, map_smul, algebraMap_smul]; exact hxe)
      exact this ▸ hx
    classical
    choose s hs1 hs2 using hy
    refine ⟨∏ c, s c, prod_mem (S := w.asIdeal.primeCompl) fun c _ => hs1 c, fun c => ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), mul_smul]
    exact Submodule.smul_mem _ _ (hs2 c)

theorem scalar_eq {O C T : Type} [CommRing O] [Field C] [Fintype T] (φ : O →+* C) (a : Oˣ) (d : T → Oˣ) (cs : T → ℤ) (x : C)
    (h : (φ a * ∏ τ, φ (d τ) ^ (-cs τ)) * x = 1) :
    φ ((a⁻¹ * ∏ τ, d τ ^ cs τ : Oˣ) : O) = x ∧ ∏ τ, φ (d τ) ^ cs τ = φ a * x ∧ x ≠ 0 := by
  have hd : ∀ τ, φ (d τ) ≠ 0 := fun τ => ((d τ).isUnit.map φ).ne_zero
  have ha : φ a ≠ 0 := (a.isUnit.map φ).ne_zero
  have hp : (∏ τ, φ (d τ) ^ cs τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hd τ)
  simp only [zpow_neg, Finset.prod_inv_distrib] at h
  have h2 : ∏ τ, φ (d τ) ^ cs τ = φ a * x := by
    field_simp at h
    linear_combination -h
  refine ⟨?_, h2, by rintro rfl; simp at h⟩
  have e : φ ((∏ τ, d τ ^ cs τ : Oˣ) : O) = ∏ τ, φ (d τ) ^ cs τ := by
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have := map_zpow (Units.map (φ : O →* C)) (d τ) (cs τ)
    exact (congrArg Units.val this).trans (Units.val_zpow_eq_zpow_val _ _)
  rw [Units.val_mul, map_mul, e, h2, map_units_inv, inv_mul_cancel_left₀ ha]

theorem smul_cancel {C M : Type} [Field C] [AddCommGroup M] [Module C M] {a x d : C} {u r : M} (hx : x ≠ 0) (hd : d = a * x)
    (h : d • u = x • r) : a • u = r :=
  smul_right_injective M hx (show x • a • u = x • r by rw [← h, hd, smul_smul, mul_comm])

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core

variable {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {l : ℕ} [Fact l.Prime]

def evG (ev : D.what₂.Tau → (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l)) :
    Gf V →* (D.what₂.Tau → GL (Fin V.rank) (PadicAlgCl l)) :=
  MonoidHom.pi fun τ => (Matrix.GeneralLinearGroup.map (ev τ)).comp (Gf V).subtype

theorem evG_rat {ev : D.what₂.Tau → (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l)}
    {inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)} (hev : ∀ τ x, ev τ (1 ⊗ₜ[D.host.F] x) = inc τ x) (γ : Formalism.L2.Theta.GQ V) :
    ∃ γE, IsRatMat V γ γE ∧ evG V ev (ratF V γ) = fun τ => Matrix.GeneralLinearGroup.map (inc τ) γE := by
  obtain ⟨γE, hγ⟩ : ∃ γE, IsRatMat V γ γE := by
    obtain ⟨x, hx⟩ := γ
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
    exact ⟨y, hy.symm⟩
  refine ⟨γE, hγ, funext fun τ => Units.ext (Matrix.ext fun a b => ?_)⟩
  have e : Units.val (Formalism.L2.Theta.finHom V (γ : Formalism.L2.Theta.GA D V)) a b = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] γE.val a b := by
    have hγ' : Formalism.L2.Theta.matHom V (γ : Formalism.L2.Theta.GA D V) = _ := hγ
    rw [Formalism.L2.Theta.finHom, MonoidHom.comp_apply, hγ']
    show (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] (γE.val a b)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  show ev τ (Units.val (Formalism.L2.Theta.finHom V (γ : Formalism.L2.Theta.GA D V)) a b) = inc τ (γE.val a b)
  rw [e]
  exact hev τ _

end Core

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

set_option maxHeartbeats 4000000 in

theorem reads_rank (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (lamW : D.what₂.Tau → ℕ → ℕ)
    (cs : D.what₂.Tau → ℤ) (hS : Shift (fun τ => lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) lamW cs) {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ)
    (hC : ChoiceOk p j w e0 false io ev bs rk (fun τ => -cs τ) kap chi) (hbs : ∀ τ, bs τ = 1) :
    ∃ R : Reads (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) N Lf kap chi) lamW (blk p j (p.R.mu w)) w,
      R.e0 = e0 ∧ R.ix = Subtype.val := by
  classical
  obtain rfl : N = (Vc D j).rank := by simpa using Fintype.card_congr rk.toEquiv
  obtain rfl : rk = OrderIso.refl _ := Subsingleton.elim _ _
  obtain ⟨hw, hL, hio, hev, hkap, hchi⟩ := hC
  obtain ⟨gramR, c0R, c0L, tie⟩ := p.charW.base.fam.tie
  obtain ⟨e, -, hce, -, hN, hD⟩ := tie.coefL j (p.R.mu w)
  have hM := tie.mapL j
  obtain ⟨hinj, hF⟩ := GlobalTheory.T.intermediateField_padic_integers_eq_norm_le_one _ Lf
  have hev' : ∀ τ, EvOk (e0.comp (labLL D τ)) (ev τ) := hev
  have hk : ∀ (k : levJ p j (p.R.mu w)) τ, Matrix.GeneralLinearGroup.map (intEmb Lf) (kap k τ) = evG (Vc D j) ev k τ := by
    intro k τ
    refine Units.ext ((hkap k τ).trans ?_)
    rw [kapMat, hbs, inv_one, Units.val_one, one_mul, mul_one]
    rfl
  have hdet : ∀ (k : levJ p j (p.R.mu w)) τ, ((Matrix.GeneralLinearGroup.det (evG (Vc D j) ev k τ) : (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))ˣ) :
      PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) = intEmb Lf (kap k τ).val.det := by
    intro k τ
    rw [← hk, RingHom.map_det]
    rfl
  have hχ : ∀ k : levJ p j (p.R.mu w), (intEmb Lf (chi k) * ∏ τ, intEmb Lf (kap k τ).val.det ^ (-cs τ)) *
      io.symm ((levChi p j (p.R.mu w) k : ℂˣ) : ℂ) = 1 := by
    intro k
    apply io.injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_one]
    exact hchi k
  have hsc := fun k : levJ p j (p.R.mu w) =>
    scalar_eq (intEmb Lf) (chi k) (fun τ => Matrix.GeneralLinearGroup.det (kap k τ)) cs _ (hχ k)
  obtain ⟨rd, h1, h2, h3, h4, h5, h6⟩ := exists_reading_lat (p.R.B.L j (p.R.mu w)).pres (labLL D) _ (c0L j) e hce
    (fun c => hLat (Vc D j) ((p.R.B.L j (p.R.mu w)).pres.y c)) (fun c => GlobalTheory.RepsCompare.isLattice_hLat _ _) hN hD hM.2.1 hM.2.2 w e0 io hw hio
    (evG (Vc D j) ev)
    (fun γ => (evG_rat (Vc D j) (fun τ => (hev' τ).1) γ).imp fun γE h => ⟨hM.1 γ γE h.1, h.2⟩)
    (fun c B hB τ a b => ⟨GlobalTheory.T.localBasis_integral_relative_adelicPoint (Vc D j) _ _ _ (hev' τ) (p.stdV j).2 _ B hB a b,
      GlobalTheory.T.adelicPoint_integral_relative_localBasis (Vc D j) _ _ _ (hev' τ) (p.stdV j).2 _ B hB a b⟩)
    lamW cs hS Lf hL
    (fun g τ a b => (IntermediateField.adjoin_le_iff.2 (by rintro _ ⟨x, rfl⟩; exact hL _)) ((hev' τ).2.2.2 _))
    (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) _ Lf kap chi) hinj hF
    (fun k τ a b => ⟨(kap k τ).val a b, congrArg (fun M : GL _ _ => M.val a b) (hk k τ)⟩)
    (fun k => ⟨(((chi k)⁻¹ * ∏ τ, Matrix.GeneralLinearGroup.det (kap k τ) ^ cs τ : (intR Lf)ˣ) : intR Lf), (hsc k).1⟩)
  refine ⟨⟨e0, Subtype.val, rd, hw, fun x => (hF _).2 ⟨hL _, ?_⟩, fun f => ⟨?_, fun k g => ?_⟩, h3, fun i f g => ?_, h5, h6⟩, rfl, rfl⟩
  · exact (GlobalTheory.T.norm_le_one_iff_integral_at_padicEmbedding_place _ _ w e0 hw _).2 ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, x, by simp⟩
  · rintro _ ⟨γ, rfl⟩ g
    exact h1 f γ g
  · have h7 := h2 f k g
    rw [lamG_apply] at h7
    have h8 := smul_cancel (hsc k).2.2 (Eq.trans (by simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, hdet k]; rfl) (hsc k).2.1) h7
    rw [← funext (hk k)] at h8
    exact h8
  · have hr : 1 ≤ i.1.2 ∧ i.1.2 ≤ (Vc D j).rank := ⟨i.2.1, i.2.2.1⟩
    have h7 := h4 f _ _ ((p.R.B.L j (p.R.mu w)).hecke.op_eq i.1 hr f) (fun a ha => funext fun τ => Units.ext
      (GlobalTheory.EvLocal.map_eq_one_of_isLocEnv (Vc D j) p.R.pl _ i.1 a _ _ (hev' τ) i.2.2.2
        ((p.R.B.L j (p.R.mu w)).hecke.hA_loc i.1 hr a ha))) g
    refine h7.trans ?_
    show _ = intEmb Lf 1 • _
    rw [map_one, one_smul]
    rfl

end Point

theorem reads_of_small : InRange fun _ _ _ _ p j P W w => SmallAt p j P w → ReadsAt p j P W w := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    EvPt.of_forall fun x hx i p _ _ j P W hD _ w _ _ _ _ => ?_⟩⟩
  choose cs hcs using hD.lam
  exact ⟨false, fun τ => -cs τ, fun e0 io ev bs rk Lf _ kap chi hC hbs =>
    reads_rank p j w W.lam cs hcs e0 io ev bs rk Lf kap chi hC hbs⟩

end GlobalTheory.FrameRead
