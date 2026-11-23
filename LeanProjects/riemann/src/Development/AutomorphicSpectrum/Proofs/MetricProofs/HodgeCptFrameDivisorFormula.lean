import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelLeftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorEquivOfBasisExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBundleUnderEquivStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlag
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticePullSplitInjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptLatticeBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.InChartIffOfDominatesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoordinateTieTransferStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptMorphismCompatStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptDescentGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamRevInvSubfamilyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGenericTriangularFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamAlgebraicIndependentFinrankStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem flagStep_colFrame_le {R M : Type} [Field R] [AddCommGroup M] [Module R M] {r : ℕ} (e : Fin r → M)
    (B : Matrix (Fin r) (Fin r) R) (hB : ∀ a b, b < a → B a b = 0) (i : ℕ) :
    flagStep R (colFrame e B) i ≤ flagStep R e i := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases h : k < a
  · rw [hB a k h, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 h)) hk, rfl⟩)

theorem flagStep_colFrame {G M : Type} [Field G] [AddCommGroup M] [Module G M] {r : ℕ} (e : Fin r → M)
    (B : Matrix (Fin r) (Fin r) G) (hB : ∀ a b, b < a → B a b = 0) (hu : IsUnit B.det) (i : ℕ) :
    flagStep G (colFrame e B) i = flagStep G e i := by
  refine le_antisymm (flagStep_colFrame_le e B hB i) ?_
  letI := Matrix.invertibleOfIsUnitDet B hu
  have ht : B.BlockTriangular id := fun a b h => hB a b h
  have hi : B⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  have h := flagStep_colFrame_le (colFrame e B) B⁻¹ (fun a b h => hi h) i
  rwa [← colFrame_mul, Matrix.mul_nonsing_inv _ hu, colFrame_one] at h

theorem linearIndependent_colFrame {G M : Type} [Field G] [AddCommGroup M] [Module G M] {r : ℕ} {e : Fin r → M}
    (he : LinearIndependent G e) (B : Matrix (Fin r) (Fin r) G) (hu : IsUnit B.det) :
    LinearIndependent G (colFrame e B) := by
  rw [Fintype.linearIndependent_iff] at he ⊢
  intro g hg
  have h0 : B.mulVec g = 0 := by
    funext l
    refine he (fun l => B.mulVec g l) ?_ l
    rw [← hg]
    simp only [colFrame, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have := Matrix.eq_zero_of_mulVec_eq_zero (hu.ne_zero) h0
  intro k
  rw [this]
  rfl

theorem exists_mat {Ω M : Type} [Field Ω] [AddCommGroup M] [Module Ω M] (W : Submodule Ω M) {r : ℕ} (C e : Fin r → M)
    (hC : LinearIndependent Ω C) (he : LinearIndependent Ω e) (hCm : ∀ k, C k ∈ W) (hem : ∀ k, e k ∈ W)
    (hr : Module.finrank Ω W = r) (hfin : Module.Finite Ω W) :
    ∃ A : Matrix (Fin r) (Fin r) Ω, IsUnit A.det ∧ ∀ k, e k = ∑ l, A l k • C l := by
  let C' : Fin r → W := fun k => ⟨C k, hCm k⟩
  let e' : Fin r → W := fun k => ⟨e k, hem k⟩
  have hC' : LinearIndependent Ω C' := LinearIndependent.of_comp W.subtype hC
  have he' : LinearIndependent Ω e' := LinearIndependent.of_comp W.subtype he
  let BC := basisOfLinearIndependentOfCardEqFinrank' C' hC' (by simp [hr])
  let Be := basisOfLinearIndependentOfCardEqFinrank' e' he' (by simp [hr])
  refine ⟨BC.toMatrix Be, ?_, fun k => ?_⟩
  · have := Module.Basis.toMatrix_mul_toMatrix_flip BC Be
    exact IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, this, Matrix.det_one])
  · have h := BC.sum_repr (e' k)
    have h2 := congrArg (Subtype.val) h
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h2
    have h3 : ∀ l, (BC l : M) = C l := fun l => by simp [BC, C']
    simp only [h3] at h2
    refine h2.symm.trans (Finset.sum_congr rfl fun l _ => ?_)
    have h4 : BC.toMatrix Be l k = BC.repr (e' k) l := by simp [Module.Basis.toMatrix_apply, Be]
    rw [h4]

theorem gen_of_mat (F₀ Ω G : Type) [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω] [Algebra Ω G] [Algebra F₀ G]
    [IsScalarTower F₀ Ω G] (E₀ E' : Type) [AddCommGroup E₀] [Module F₀ E₀] [AddCommGroup E'] [Module G E']
    (j₀ : E₀ →+ E') (S : Type) [Finite S] (r : S → ℕ) (V₀ : S → Submodule F₀ E₀) (c : ∀ s, Fin (r s) → E₀)
    (b : ∀ s, Fin (r s) → E') (U : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G)
    (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (d : ℕ)
    (hc : ∀ s, LinearIndependent F₀ (c s) ∧ Submodule.span F₀ (Set.range (c s)) = V₀ s)
    (hsemi : ∀ (a : F₀) e, j₀ (a • e) = algebraMap F₀ G a • j₀ e)
    (hlin : ∀ s, LinearIndependent G fun k => j₀ (c s k)) (hU : IsGenFam Ω G U) (hA : ∀ s, IsUnit (A s).det)
    (hb : ∀ s k, b s k = ∑ l, ((A s).map (algebraMap Ω G) * U s) l k • j₀ (c s l)) (hd : 0 < d)
    (hfin : Module.finrank F₀ Ω = d) : GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω' := G) j₀ V₀ b d := by
  obtain ⟨u', B, hu', hB, hBt, hAB⟩ := GlobalTheory.T.exists_generic_triangular_factorization Ω G S r U A hU hA
  obtain ⟨hind, hdeg⟩ := GlobalTheory.T.isGenFam_algebraicIndependent_finrank F₀ Ω G S r u' d hd hfin hu'
  have hbe : ∀ s, b s = colFrame (colFrame (fun k => j₀ (c s k)) (u' s)) (B s) := fun s => by
    rw [← colFrame_mul, ← hAB]
    funext k
    exact hb s k
  have hu'd : ∀ s, IsUnit (u' s).det := fun s => by
    rw [Matrix.det_of_lowerTriangular _ fun a b h => hu'.2.1 s a b h]
    simp [hu'.1 s]
  refine ⟨c, u', hc, hsemi, hlin, fun s => ?_, hu'.1, hu'.2.1, fun s i => ?_, hind, hd, hdeg⟩
  · rw [hbe]
    exact linearIndependent_colFrame (linearIndependent_colFrame (hlin s) _ (hu'd s)) _ (hB s)
  · rw [hbe, flagStep_colFrame _ _ (hBt s) (hB s)]
    rfl

theorem spMap_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    spMap (dualMap (b.comp a)) = spMap (dualMap b) ≫ spMap (dualMap a) := by
  have e : dualMap (b.comp a) = (dualMap b).comp (dualMap a) := RingHom.ext fun x => by ext <;> simp [dualMap]
  rw [e]
  simp only [spMap]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem gen_of_mat' (F₀ Ω G : Type) [Field F₀] [Field Ω] [Field G] [Algebra Ω G] (ι : F₀ →+* Ω) (fn : F₀ →+* G)
    (hι : (algebraMap Ω G).comp ι = fn) (E₀ E' : Type) [AddCommGroup E₀] [Module F₀ E₀] [AddCommGroup E'] [Module G E']
    (j₀ : E₀ →+ E') (S : Type) [Finite S] (r : S → ℕ) (V₀ : S → Submodule F₀ E₀) (c : ∀ s, Fin (r s) → E₀)
    (b : ∀ s, Fin (r s) → E') (U : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G)
    (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (d : ℕ)
    (hc : ∀ s, LinearIndependent F₀ (c s) ∧ Submodule.span F₀ (Set.range (c s)) = V₀ s)
    (hsemi : ∀ (a : F₀) e, j₀ (a • e) = fn a • j₀ e)
    (hlin : ∀ s, LinearIndependent G fun k => j₀ (c s k)) (hU : IsGenFam Ω G U) (hA : ∀ s, IsUnit (A s).det)
    (hb : ∀ s k, b s k = ∑ l, ((A s).map (algebraMap Ω G) * U s) l k • j₀ (c s l)) (hd : 0 < d)
    (hfin : letI := ι.toAlgebra; Module.finrank F₀ Ω = d) :
    letI := fn.toAlgebra
    GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω' := G) j₀ V₀ b d := by
  letI := ι.toAlgebra
  letI := fn.toAlgebra
  haveI : IsScalarTower F₀ Ω G := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun hι a).symm
  exact gen_of_mat F₀ Ω G E₀ E' j₀ S r V₀ c b U A d hc hsemi hlin hU hA hb hd hfin

set_option maxHeartbeats 1000000 in

theorem exists_colFlags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → 𝔐.IsCover d → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → Submodule.span (GenField Ω (rk (CMType H) D.p D.q)) (Set.range j) = ⊤ → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ∃ Fl : 𝔐'.Flag, Fl.deg = d ∧ ColFlags 𝔐 bW bO j Fl := by
  classical
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d hF hC 𝔐' pr j hO hspan hV
  obtain ⟨hvb, hcc, htw, -⟩ := hF
  obtain ⟨hdom, hff, hcst, hext, hpt⟩ := id hO
  have htie₀ : CoordTie ℤ 𝔐'.ξ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) := by
    convert 𝔐'.tie using 1
    exact Subsingleton.elim _ _
  have htie := GlobalTheory.T.hodgeCpt_dual_frame_generic E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n φ 𝔐'.X 𝔐'.ξ htie₀
  have hch := GlobalTheory.T.inChart_iff_of_dominates' 𝔐.X 𝔐'.X Ω (GenField Ω (rk (CMType H) D.p D.q)) 𝔐.ξ 𝔐'.ξ pr
    (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ((k : K₀) → J₀ k) (seg x₀) 𝔐.tie htie₀.gen hdom
  have hfl := GlobalTheory.T.flag_frames_generic_model_left 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀) (CMType H ⊕ CMType H)
    (rk (CMType H) D.p D.q) (VV 𝔐) (LL 𝔐) m n φ (cc 𝔐 bW bO) 𝔐'.X 𝔐'.ξ pr 𝔐.tie 𝔐.all hvb htw hcc htie 𝔐'.all hdom hch
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.tensor_equiv_of_basis_extension Ω (GenField Ω (rk (CMType H) D.p D.q)) 𝔐.Li 𝔐'.Li j hext.1 hext.2 hspan
  have hjΦ : Φ.toLinearMap.toAddMonoidHom.comp
      (TensorProduct.mk Ω (GenField Ω (rk (CMType H) D.p D.q)) 𝔐.Li 1).toAddMonoidHom = j := AddMonoidHom.ext hΦ

  have hW : ∀ τ, (𝔐'.V (.inl τ)).IsFlagVBOn Set.univ (fun k : Fin D.p =>
      ∑ a, genU Ω (rk (CMType H) D.p D.q) (.inl τ) a k • j (bW τ a)) := by
    intro τ
    have h1 := GlobalTheory.T.lattice_pull_split_injection 𝔐.X 𝔐'.X Ω (GenField Ω (rk (CMType H) D.p D.q)) 𝔐.ξ 𝔐'.ξ pr 𝔐.Li (EE 𝔐) (inW 𝔐)
      (LinearMap.fst Ω _ _) (𝔐.V (.inl τ)) D.p (fun a => (bW τ a : 𝔐.Li))
      (genU Ω (rk (CMType H) D.p D.q) (.inl τ)) (LinearMap.ext fun _ => rfl) (hfl (.inl τ))
    have h2 := GlobalTheory.T.flag_bundle_under_equiv 𝔐.X 𝔐'.X Ω (GenField Ω (rk (CMType H) D.p D.q)) 𝔐.ξ 𝔐'.ξ pr 𝔐.Li _ 𝔐'.Li
      (𝔐.V (.inl τ)) _ Φ Set.univ _ _ h1
    rw [hjΦ, ← hV] at h2
    have e : (fun k : Fin D.p => ∑ a, genU Ω (rk (CMType H) D.p D.q) (.inl τ) a k • j (bW τ a)) =
        fun k => Φ (∑ l, genU Ω (rk (CMType H) D.p D.q) (.inl τ) l k •
          TensorProduct.mk Ω (GenField Ω (rk (CMType H) D.p D.q)) 𝔐.Li 1 (bW τ l)) := by
      funext k
      rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hΦ]
    rw [e]
    exact h2

  have hv : ∀ τ, ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, bO τ a (v b) = if a = b then 1 else 0 := by
    intro τ
    obtain ⟨B⟩ := nonempty_basis_Vgen 𝔐 (.inr τ)
    have := Module.Finite.of_basis B
    refine ⟨fun b => (Module.evalEquiv Ω _).symm ((bO τ).coord b), fun a b => ?_⟩
    rw [Module.apply_evalEquiv_symm_apply, Module.Basis.coord_apply, (bO τ).repr_self, Finsupp.single_apply]
  choose v hv using hv
  have hvu : ∀ τ (v' : Fin D.q → 𝔐.Vgen (.inr τ)), (∀ a b, bO τ a (v' b) = if a = b then 1 else 0) → v' = v τ := by
    intro τ v' h'
    obtain ⟨B⟩ := nonempty_basis_Vgen 𝔐 (.inr τ)
    have := Module.Finite.of_basis B
    funext b
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff Ω]
    intro f
    have hf : f ∈ Submodule.span Ω (Set.range (bO τ)) := by rw [(bO τ).span_eq]; trivial
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨a, rfl⟩ := hf; simp [h', hv]
    | zero => simp
    | add f g _ _ h1 h2 => simp only [LinearMap.add_apply, h1, h2, add_zero]
    | smul t f _ h1 => simp only [LinearMap.smul_apply, h1, smul_zero]

  have hO' : ∀ τ, (𝔐'.V (.inr τ)).IsFlagVBOn Set.univ (fun k : Fin D.q =>
      colFrame (fun a => j (v τ a)) (genU Ω (rk (CMType H) D.p D.q) (.inr τ) : Matrix (Fin D.q) (Fin D.q) _)ᵀ⁻¹ k.rev) := by
    intro τ
    have h1 := GlobalTheory.T.lattice_pull_split_injection 𝔐.X 𝔐'.X Ω (GenField Ω (rk (CMType H) D.p D.q)) 𝔐.ξ 𝔐'.ξ pr _ (EE 𝔐) (inO 𝔐 τ)
      ((LinearMap.proj τ).comp (LinearMap.snd Ω _ _)) (omBundle 𝔐 τ) D.q (fun a => bO τ a)
      (genU Ω (rk (CMType H) D.p D.q) (.inr τ)) (LinearMap.ext fun _ => by simp [inO]) (hfl (.inr τ))
    rw [hV]
    exact GlobalTheory.T.hodgeCpt_lattice_base_change E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 τ 𝔐'.X _ 𝔐'.ξ pr 𝔐'.Li j (bO τ) (v τ) _ hext hdom (hv τ)
      (fun a => genU_diag (r := rk (CMType H) D.p D.q) (.inr τ) a) (fun a b h => genU_above (r := rk (CMType H) D.p D.q) (.inr τ) a b h) h1

  obtain ⟨ι, hι, hdomι, hfin⟩ := GlobalTheory.T.hodgeCpt_morphism_compat E H D l Xo c Y S Ω _ K₀ _ J₀ _ x₀ _ 𝔐 𝔐' pr _ j d hO hC
  obtain ⟨Li₀, _, _, M₀, j₁, V₀, c₀, hpt₁, hext₁, hV₀, hc₀⟩ :=
    GlobalTheory.T.hodgeCpt_descent_generic_point E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 𝔐'.Ω₀ 𝔐'.ξ₀ ι 𝔐'.gen₀ hdomι
  have hjinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun e he => ?_
    by_contra hne
    have h1 := hext.2 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  have hrefl : ∀ s w, w ∈ 𝔐.Vgen s ↔ j w ∈ 𝔐'.Vgen s := by
    intro s w
    refine ⟨hO.map_Vgen s, fun h => (Submodule.mem_iInf _).2 fun t => ?_⟩
    have h1 : 𝔐'.ρ t (j w) - 𝔐'.emb s t • j w = 0 := (Submodule.mem_iInf _).1 h t
    show 𝔐.ρ t w - 𝔐.emb s t • w = 0
    have e : 𝔐'.emb s t = algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (𝔐.emb s t) := by
      show 𝔐'.cst _ = _
      rw [hcst]; rfl
    apply hjinj
    rw [map_sub, map_zero, hO.map_act, hext.1, ← e]
    exact h1

  let eb : ∀ s, Fin (labelRk D s) → 𝔐.Li := fun s => match s with
    | .inl τ => fun a => (bW τ a : 𝔐.Li)
    | .inr τ => fun a => (v τ a.rev : 𝔐.Li)
  have heb : ∀ s, LinearIndependent Ω (eb s) ∧ ∀ k, eb s k ∈ 𝔐.Vgen s := by
    rintro (τ | τ)
    · exact ⟨(bW τ).linearIndependent.map' (𝔐.Vgen (.inl τ)).subtype (Submodule.ker_subtype _), fun k => (bW τ k).2⟩
    · have h1 : LinearIndependent Ω (v τ) := LinearIndependent.of_pairwise_dual_eq_zero_one (v τ) (bO τ)
        (fun a b hab => (hv τ a b).trans (if_neg hab)) (fun a => by rw [hv, if_pos rfl])
      have h2 := h1.map' (𝔐.Vgen (.inr τ)).subtype (Submodule.ker_subtype _)
      exact ⟨h2.comp Fin.rev Fin.rev_injective, fun k => (v τ k.rev).2⟩
  have hA : ∀ s, ∃ A : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) Ω, IsUnit A.det ∧
      ∀ k, eb s k = ∑ l, A l k • j₁ (c₀ s l) := by
    intro s
    obtain ⟨B⟩ := nonempty_basis_Vgen 𝔐 s
    exact exists_mat (𝔐.Vgen s) _ _ (hext₁.2 _ _ (hc₀ s).1) (heb s).1
      (fun k => (hV₀ s _).1 (by rw [← (hc₀ s).2]; exact Submodule.subset_span ⟨k, rfl⟩)) (heb s).2
      (by simpa using Module.finrank_eq_card_basis B) (Module.Finite.of_basis B)
  choose A hAu hAe using hA
  let U : ∀ s, Matrix (Fin (rk (CMType H) D.p D.q s)) (Fin (rk (CMType H) D.p D.q s))
      (GenField Ω (rk (CMType H) D.p D.q)) := fun s =>
    if Sum.isRight s = true then revInv (genU Ω (rk (CMType H) D.p D.q) s) else genU Ω (rk (CMType H) D.p D.q) s
  have hU : IsGenFam Ω (GenField Ω (rk (CMType H) D.p D.q)) U :=
    GlobalTheory.T.isGenFam_revInv_subfamily Ω _ _ (rk (CMType H) D.p D.q) (genU Ω (rk (CMType H) D.p D.q)) (fun s => Sum.isRight s = true)
      (genU_isGenFam Ω _)
  have hUl : ∀ τ, U (.inl τ) = genU Ω (rk (CMType H) D.p D.q) (.inl τ) := fun τ => if_neg (by simp)
  have hUr : ∀ τ, U (.inr τ) = revInv (genU Ω (rk (CMType H) D.p D.q) (.inr τ)) := fun τ => if_pos (by simp)
  let b : ∀ s, Fin (labelRk D s) → 𝔐'.Li := fun s k => ∑ a, U s a k • j (eb s a)
  have hbW : ∀ τ k, b (.inl τ) k = ∑ a, genU Ω (rk (CMType H) D.p D.q) (.inl τ) a k • j (bW τ a) := fun τ k => by
    show ∑ a, U (.inl τ) a k • j (bW τ a) = _
    rw [hUl]
  have hbO : ∀ τ (k : Fin D.q), b (.inr τ) k = colFrame (fun a => j (v τ a))
      (genU Ω (rk (CMType H) D.p D.q) (.inr τ) : Matrix (Fin D.q) (Fin D.q) _)ᵀ⁻¹ k.rev := fun τ k => by
    show ∑ a : Fin D.q, U (.inr τ) a k • j (v τ a.rev) = _
    rw [hUr]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun a => rfl
  have hb : ∀ s k, b s k = ∑ l, ((A s).map (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) * U s) l k •
      (j.comp j₁) (c₀ s l) := by
    intro s k
    have h1 : ∀ a, j (eb s a) = ∑ l, algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (A s l a) •
        (j.comp j₁) (c₀ s l) := fun a => by
      rw [hAe s a, map_sum]
      exact Finset.sum_congr rfl fun l _ => hext.1 _ _
    show ∑ a, U s a k • j (eb s a) = _
    simp only [h1, Matrix.mul_apply, Matrix.map_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]
  have hsub : ∀ s, (𝔐'.V s).IsFlagVBOn Set.univ (b s) := by
    rintro (τ | τ)
    · rw [show b (.inl τ) = _ from funext (hbW τ)]
      exact hW τ
    · rw [show b (.inr τ) = _ from funext (hbO τ)]
      exact hO' τ
  have hjpt : ∀ e, (𝔐'.M.pt ((j.comp j₁) e)).left ≫ 𝔐'.m.φ = spMap (dualMap 𝔐'.fn) ≫ (M₀.pt e).left := by
    intro e
    show (𝔐'.M.pt (j (j₁ e))).left ≫ _ = _
    rw [hpt, hpt₁ e, ← hι, spMap_dual_comp ι (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))), Category.assoc]
  have hgen : letI := 𝔐'.fn.toAlgebra
      GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω' := GenField Ω (rk (CMType H) D.p D.q)) (j.comp j₁) V₀ b d := by
    exact gen_of_mat' 𝔐'.Ω₀ Ω (GenField Ω (rk (CMType H) D.p D.q)) ι 𝔐'.fn hι Li₀ 𝔐'.Li (j.comp j₁) _ (labelRk D) V₀ c₀ b U A d
      hc₀ (fun a e => by
        show j (j₁ (a • e)) = 𝔐'.fn a • j (j₁ e)
        rw [hext₁.1, hext.1, ← hι]; rfl)
      (fun s => hext.2 _ _ (hext₁.2 _ _ (hc₀ s).1)) hU hAu hb hC.1 hfin
  have hw : ∀ τ, wBlock (gMat D.p D.q Ω τ) = genU Ω (rk (CMType H) D.p D.q) (.inl τ) := fun τ => by
    ext a b
    exact GenMat.gMat_w Ω τ a b
  have ho : ∀ τ, omBlock (gMat D.p D.q Ω τ) = genU Ω (rk (CMType H) D.p D.q) (.inr τ) := fun τ => by
    ext a b
    exact GenMat.gMat_om Ω τ a b
  refine ⟨{ b := b, sub := hsub, Li₀ := Li₀, M₀ := M₀, j := j.comp j₁, j_pt := hjpt, V₀ := V₀,
            V₀_mem := fun s e => (hV₀ s e).trans (hrefl s (j₁ e)), deg := d, generic := hgen }, rfl,
    fun τ k => ?_, fun τ v' hv' k => ?_⟩
  · rw [hw]
    exact hbW τ k
  · rw [ho, hvu τ v' hv']
    exact hbO τ k

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
