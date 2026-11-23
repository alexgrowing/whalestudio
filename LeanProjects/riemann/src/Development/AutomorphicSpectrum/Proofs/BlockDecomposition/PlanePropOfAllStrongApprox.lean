import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeFrameEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOfConjEq

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology Sa2 Matrix
  GlobalTheory.CompanionTheory.StrongApproxSub
open Formalism.UG (UJ bc)
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {K : Matrix (Fin 2) (Fin 2) E} {a : E}
  {V : Matrix (Fin M) (Fin 2) E} {P : Matrix (Fin 2) (Fin M) E}

theorem sig_incl (e : E) :
    inclR (F := F) (E := E) (AF F) ((σ : E →+* E) e) = sigR (AF F) σ (inclR (F := F) (E := E) (AF F) e) := by
  simp [sigR, inclR]

theorem frameA (h : IsFrame (σ : E →+* E) J K a V P) :
    IsFrame (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) K) (inclR (F := F) (E := E) (AF F) a) (V.map (inclR (F := F) (E := E) (AF F)))
      (P.map (inclR (F := F) (E := E) (AF F))) :=
  h.map (inclR (F := F) (E := E) (AF F)) sig_incl

def iota (h : IsFrame (σ : E →+* E) J K a V P) : HA (AF F) σ K →* HA (AF F) σ J :=
  uHom (frameA h)

theorem mt_iota (h : IsFrame (σ : E →+* E) J K a V P) (g : HA (AF F) σ K) :
    mt (iota h g) = emb0 (V.map (inclR (F := F) (E := E) (AF F))) (P.map (inclR (F := F) (E := E) (AF F))) (mt g) := rfl

theorem continuous_iota (h : IsFrame (σ : E →+* E) J K a V P) :
    Continuous (iota (F := F) h) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous (embHom (frameA (F := F) h).pv) :=
    continuous_const.add (((continuous_const.matrix_mul
      (continuous_id.sub continuous_const))).matrix_mul continuous_const)
  have hu := Continuous.units_map _ hm
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

theorem iota_adelic (h : IsFrame (σ : E →+* E) J K a V P) {g : HA (AF F) σ K}
    (hg : g ∈ SUAdelic σ K) : iota h g ∈ SUAdelic σ J := by
  refine StrongApprox.mem_SUAdelic.2 ?_
  have := StrongApprox.mem_SUAdelic.1 hg
  change (mt (iota h g)).det = 1
  rw [mt_iota, det_frame_embedding (frameA h).pv]
  exact this

theorem iota_rat (h : IsFrame (σ : E →+* E) J K a V P) {γ : HA (AF F) σ K}
    (hγ : γ ∈ SURat σ K) : iota h γ ∈ SURat σ J := by
  refine ⟨iota_adelic h hγ.1, ?_⟩
  obtain ⟨u, hu, e⟩ : (γ : HR (AF F) σ K).1 ∈ (UJ (σ : E →+* E) K).map (bc (inclR (F := F) (E := E) (AF F))) := hγ.2
  change (iota h γ : HR (AF F) σ J).1 ∈ (UJ (σ : E →+* E) J).map (bc (inclR (F := F) (E := E) (AF F)))
  refine ⟨(uHom h ⟨u, hu⟩).1, (uHom h ⟨u, hu⟩).2, Units.ext ?_⟩
  have e' : ((γ : HR (AF F) σ K).1 : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) =
      (u : Matrix (Fin 2) (Fin 2) E).map (inclR (F := F) (E := E) (AF F)) := by
    rw [← e]; rfl
  change (emb0 V P (u : Matrix (Fin 2) (Fin 2) E)).map (inclR (F := F) (E := E) (AF F)) =
    emb0 (V.map (inclR (F := F) (E := E) (AF F))) (P.map (inclR (F := F) (E := E) (AF F)))
      ((γ : HR (AF F) σ K).1 : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E))
  rw [e']
  exact frame_embedding_map _ _ _ _

theorem iota_supp (h : IsFrame (σ : E →+* E) J K a V P) {u₀ u₁ : Fin M → E}
    (hP : ∀ x : Fin M → E, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ P.mulVec x = 0) {ε : AF F}
    {g : HA (AF F) σ K} (hg : g ∈ SUSupp σ K ε) : iota h g ∈ PlaneSupp σ J ε u₀ u₁ := by
  obtain ⟨g1, g2⟩ := mem_SUSupp.1 hg
  refine ⟨mem_SUSupp.2 ⟨iota_adelic h g1, ?_⟩, fun x h0 h1 => ?_⟩
  · have e : mt (iota h g) - 1 =
        V.map (inclR (F := F) (E := E) (AF F)) * (mt g - 1) * P.map (inclR (F := F) (E := E) (AF F)) := by
      rw [mt_iota, emb0, add_sub_cancel_left]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, g2]
  · have hx : P.mulVec x = 0 := (hP x).1 ⟨h0, h1⟩
    have hv : (P.map (inclR (F := F) (E := E) (AF F))).mulVec (vA x) = 0 := by
      funext k
      have := RingHom.map_mulVec (inclR (F := F) (E := E) (AF F)) P x k
      rw [hx] at this
      have e : vA (F := F) x = (inclR (F := F) (E := E) (AF F)) ∘ x := rfl
      rw [e]
      simpa using this.symm
    change (mt (iota h g)).mulVec (vA x) = vA x
    rw [mt_iota, emb0, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_zero, add_zero]

theorem iota_surj (h : IsFrame (σ : E →+* E) J K a V P) (ha : a ≠ 0) (hJ : J.det ≠ 0) {u₀ u₁ : Fin M → E}
    (hP : ∀ x : Fin M → E, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ P.mulVec x = 0) {δ : AF F}
    {g : HA (AF F) σ J} (hg : g ∈ PlaneSupp σ J δ u₀ u₁) : ∃ y ∈ SUSupp σ K δ, iota h y = g := by
  obtain ⟨g1, g2⟩ := hg
  obtain ⟨g1a, g1b⟩ := mem_SUSupp.1 g1
  have hq0 : P * (1 - V * P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h.pv, Matrix.one_mul, sub_self]
  have hmap : 1 - V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F)) = (1 - V * P).map (inclR (F := F) (E := E) (AF F)) := by
    have h1 : (1 : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (E := E) (AF F)) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    have h2 : (V * P).map (inclR (F := F) (E := E) (AF F)) = V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F)) :=
      Matrix.map_mul
    rw [← h1, ← h2]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hq : mt g * (1 - V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F))) =
      1 - V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F)) := by
    rw [hmap]
    ext i j
    have hx : P.mulVec (fun l => (1 - V * P : Matrix (Fin M) (Fin M) E) l j) = 0 := by
      funext k
      exact congrFun (congrFun hq0 k) j
    have := g2 _ ((hP _).2 hx).1 ((hP _).2 hx).2
    exact congrFun this i
  have hab : inclR (F := F) (E := E) (AF F) a⁻¹ * inclR (F := F) (E := E) (AF F) a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have hL : (J⁻¹).map (inclR (F := F) (E := E) (AF F)) * JR (AF F) J = 1 := by
    have e : (J⁻¹).map (inclR (F := F) (E := E) (AF F)) * J.map (inclR (F := F) (E := E) (AF F)) = (J⁻¹ * J).map (inclR (F := F) (E := E) (AF F)) :=
      Matrix.map_mul.symm
    change (J⁻¹).map (inclR (F := F) (E := E) (AF F)) * J.map (inclR (F := F) (E := E) (AF F)) = 1
    rw [e, Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hJ)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨y, hy1', hy2'⟩ : ∃ y : HA (AF F) σ K, iota h y = g ∧
      mt y = P.map (inclR (F := F) (E := E) (AF F)) * mt g * V.map (inclR (F := F) (E := E) (AF F)) :=
    exists_preimage (frameA (F := F) h) hab hL g hq
  refine ⟨y, mem_SUSupp.2 ⟨StrongApprox.mem_SUAdelic.2 ?_, ?_⟩, hy1'⟩
  · have h1 : (mt g).det = 1 := StrongApprox.mem_SUAdelic.1 g1a
    rw [← hy1', mt_iota, det_frame_embedding (frameA h).pv] at h1
    exact h1
  · have e : mt y - 1 =
        P.map (inclR (F := F) (E := E) (AF F)) * (mt g - 1) * V.map (inclR (F := F) (E := E) (AF F)) := by
      rw [hy2', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, (frameA (F := F) h).pv]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, g1b]

end Adelic

theorem plane_prop_of_strong_approx : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ β : F, β ≠ 0 → HermitianPlaneStrongApprox σ β) → Sa2.PropPlane := by
  intro hSA F E _ _ _ _ _ σ hcm M J _ hJ S₁ S₂ ε hε u₀ u₁ hnd hnc T₁ T₂ δ hδ
  obtain ⟨β, a, V, P, hβ, ha, h, hP⟩ := exists_frame hcm hJ hnd
  have img : ∀ η : AF F, PlaneSupp σ J η u₀ u₁ = iota h '' SUSupp σ (J2 E β) η := by
    intro η
    ext g
    constructor
    · intro hg
      obtain ⟨y, hy, e⟩ := iota_surj h ha hJ.2 hP hg
      exact ⟨y, hy, e⟩
    · rintro ⟨y, hy, rfl⟩
      exact iota_supp h hP hy
  have hnc2 : ¬ IsCompact (SUSupp σ (J2 E β) ε) := fun hc =>
    hnc (by rw [img ε]; exact hc.image (continuous_iota h))
  have hcl := hSA F E σ hcm β hβ S₁ S₂ ε hε hnc2 T₁ T₂ δ hδ
  rw [img δ]
  rintro _ ⟨g, hg, rfl⟩
  refine closure_mono ?_ (image_closure_subset_closure_image (continuous_iota h) ⟨g, hcl hg, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, k, hk, rfl⟩, rfl⟩
  exact ⟨iota h γ, iota_rat h hγ, iota h k, (iota_supp h hP hk).1, map_mul _ _ _⟩

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
