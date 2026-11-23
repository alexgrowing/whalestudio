import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndSign
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjEquivApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionSelfDualOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicHermitianFormGaloisMemOfMemCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLinearApproxTower
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SelfDualLatticeOccurs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

theorem genus_traceIdeal (E : Type) [Field E] [NumberField E] (ξ : E) (hξ : ξ ≠ 0) :
    ∃ J : FractionalIdeal (𝓞 E)⁰ E, J ≠ 0 ∧
      ∀ z : E, z ∈ J ↔ ∀ s : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (ξ * (z * (s : E))) = k := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  refine ⟨FractionalIdeal.spanSingleton _ ξ⁻¹ * FractionalIdeal.dual ℤ ℚ 1,
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 (inv_ne_zero hξ))
      (FractionalIdeal.dual_ne_zero ℤ ℚ h1), fun z => ⟨fun hz s => ?_, fun hz => ?_⟩⟩
  · obtain ⟨y, hy, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hz
    rw [FractionalIdeal.mem_dual h1] at hy
    obtain ⟨k, hk⟩ := hy (s : E) ((FractionalIdeal.mem_one_iff _).2 ⟨s, rfl⟩)
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast] at hk
    rw [hk]
    congr 1
    field_simp
  · refine FractionalIdeal.mem_singleton_mul.2 ⟨ξ * z, ?_, by field_simp⟩
    rw [FractionalIdeal.mem_dual h1]
    intro a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨k, hk⟩ := hz s
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk, mul_assoc]

theorem genus_trace_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (ξ : E) (J : FractionalIdeal (𝓞 E)⁰ E)
    (hJ : ∀ z : E, z ∈ J ↔ ∀ s : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (ξ * (z * (s : E))) = k)
    (L : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    (∀ y ∈ L, herm G v y ∈ J) ↔ ∀ y ∈ L, ∃ k : ℤ, Algebra.trace ℚ E (ξ * herm G v y) = k := by
  constructor
  · intro h y hy
    simpa using (hJ _).1 (h y hy) 1
  · intro h y hy
    refine (hJ _).2 fun s => ?_
    have hi : IsIntegral ℤ (cc (s : E)) :=
      s.isIntegral_coe.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)
    have hcc : cc (cc (s : E)) = s := IsCMField.complexConj_apply_apply E _
    have := h _ (L.smul_mem (⟨cc (s : E), hi⟩ : 𝓞 E) hy)
    change ∃ k : ℤ, Algebra.trace ℚ E (ξ * herm G v (cc (s : E) • y)) = k at this
    rwa [GlobalTheory.HermModel.herm_smul_right, hcc] at this

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

theorem genus_hermA_shift (N : ℕ) (x y w w' : Fin n → AdLat.RA F E) :
    AdLat.hermA c G (x + N • w) (y + N • w') =
      AdLat.hermA c G x y + N • (AdLat.hermA c G w (y + N • w') + AdLat.hermA c G x w') := by
  simp only [AdLat.hermA, Pi.add_apply, Pi.smul_apply, map_add, map_nsmul, smul_add, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [nsmul_eq_mul]
  ring

theorem genus_fv_mulVec (γ : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    AdLat.fv F (γ *ᵥ v) = γ.map (inclR (F := F) (Af F)) *ᵥ AdLat.fv F v := by
  funext i
  exact RingHom.map_mulVec (inclR (F := F) (Af F)) γ v i

end

theorem genus_translate (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
    (n : ℕ) (c : E ≃ₐ[F] E) (hc : ∀ x, c x = cc x) (G : Matrix (Fin n) (Fin n) E) (hG : ∀ a b, cc (G a b) = G b a)
    (hdet : G.det ≠ 0) (ξ : E) (hξ : ξ ≠ 0) (L Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hsd : ∀ v, (∀ y ∈ L, ∃ k : ℤ, Algebra.trace ℚ E (ξ * herm G v y) = k) ↔ v ∈ L)
    (g : GL (Fin n) (AdLat.RA F E))
    (hg : ∀ x y, AdLat.hermA c G (g.1 *ᵥ x) (g.1 *ᵥ y) = AdLat.hermA c G x y)
    (hΛ : (Λ : Set (Fin n → E)) = AdLat.latOf F g.1 L) :
    Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      (∀ v, (∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (ξ * herm G v y) = k) ↔ v ∈ Λ) ∧
      ∃ f : ℕ → (L →ₗ[𝓞 E] Λ),
        (∀ N : ℕ, 0 < N → ∀ a : L, ∃ w ∈ AdLat.hat F (L : Set (Fin n → E)),
          AdLat.fv F (f N a : Fin n → E) = g.1 *ᵥ (AdLat.fv F (a : Fin n → E) + N • w)) ∧
        (∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ v, f (N * m) a = f N a + N • v) ∧
        (∀ N : ℕ, 0 < N → (∀ a, (∃ v, f N a = N • v) ↔ ∃ v, a = N • v) ∧ ∀ a', ∃ a v, a' = f N a + N • v) ∧
        ∀ N : ℕ, 0 < N → ∀ a a' : L, ∃ z : ℤ, Algebra.trace ℚ E (ξ * herm G (f N a) (f N a')) -
          Algebra.trace ℚ E (ξ * herm G a a') = N * z := by
  obtain ⟨J, hJ0, hJ⟩ := genus_traceIdeal E ξ hξ
  have hh : ∀ x y : Fin n → E, (∑ a, ∑ b, x a * G a b * c (y b)) = herm G x y := fun x y => by
    simp only [hc, herm]
  have hcc : ∀ x, c (c x) = x := fun x => by
    rw [hc, hc]; exact IsCMField.complexConj_apply_apply E _
  have hG' : ∀ a b, c (G a b) = G b a := fun a b => by rw [hc, hG]
  have hL : ∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L := fun v => by
    simp only [hh]
    rw [genus_trace_iff G ξ J hJ, hsd]
  obtain ⟨Λ', h1, hΛfg, hΛsp, -⟩ := AdLat.exists_lattice_latOf F E n L g hfg hsp
  obtain rfl : Λ = Λ' := SetLike.coe_injective (hΛ.trans h1.symm)
  obtain ⟨f, hf1, hf2, hf3⟩ := AdLat.exists_linear_approx_tower F E n L g Λ hfg hsp hΛ
  refine ⟨hΛfg, hΛsp, fun v => ?_, f, hf1, hf2, hf3, fun N hN a a' => ?_⟩
  · have := AdLat.latOf_selfDual F E n L c G J g hfg hsp hcc hG' hdet hJ0 hL hg v
    simp only [hh, ← hΛ, SetLike.mem_coe] at this
    rw [← genus_trace_iff G ξ J hJ, this]
  · obtain ⟨w, hw, e⟩ := hf1 N hN a
    obtain ⟨w', hw', e'⟩ := hf1 N hN a'
    have hd := AdLat.hat_selfDual F E n L c G J hfg hsp hcc hG' hdet hJ0 hL
    have hr := (AdLat.hat_rational_points_and_approx F E n L hfg hsp).1
    have hm : ∀ z ∈ AdLat.hat F (L : Set (Fin n → E)), ∀ z' ∈ AdLat.hat F (L : Set (Fin n → E)),
        AdLat.hermA c G z z' ∈ AdLat.hat1 F (J : Set E) := fun z hz z' hz' =>
      AdLat.adelicHermitianFormGalois_mem_of_mem_completion c G ((hd z).2 hz) hz'
    have hs := add_mem (hm w hw _ (add_mem ((hr _).2 a'.2) (nsmul_mem hw' N))) (hm _ ((hr _).2 a.2) w' hw')
    have key := genus_hermA_shift c G N (AdLat.fv F (a : Fin n → E)) (AdLat.fv F (a' : Fin n → E)) w w'
    rw [← hg, ← e, ← e', AdLat.hermA_fv_fv, AdLat.hermA_fv_fv, hh, hh] at key
    have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    set t : E := (N : E)⁻¹ * (herm G (f N a) (f N a') - herm G a a') with ht
    have ht' : N • t = herm G (f N a) (f N a') - herm G a a' := by
      rw [nsmul_eq_mul, ht, mul_inv_cancel_left₀ hN']
    have htJ : t ∈ J := by
      rw [← (AdLat.adelicCompletion_fractionalIdeal_properties F E).2.1]
      convert hs using 1
      apply smul_right_injective _ hNF
      simp only [Nat.cast_smul_eq_nsmul]
      rw [← TensorProduct.tmul_smul, ht', TensorProduct.tmul_sub, key, add_sub_cancel_left]
    obtain ⟨k, hk⟩ := (hJ t).1 htJ 1
    refine ⟨k, ?_⟩
    rw [← map_sub, ← mul_sub, ← ht', ← hk, mul_smul_comm, map_nsmul, nsmul_eq_mul]
    simp

theorem genus_mem_UJ {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (σ : E →+* E) (hσ : ∀ x, σ x = cc x)
    (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E)
    (h : ∀ u v, herm (-J.transpose) (γ.1 *ᵥ u) (γ.1 *ᵥ v) = herm (-J.transpose) u v) : γ ∈ Formalism.UG.UJ σ J := by
  change Formalism.UG.cT _ _ * _ * _ = _
  ext i j
  have h := h (Pi.single j 1) (Pi.single i 1)
  simp only [herm, ← hσ, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.neg_apply,
    Matrix.transpose_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_inj] at h
  simp only [Pi.single_apply, apply_ite σ,
    map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem genus_bc_mem_HR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E)
    (h : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) : Formalism.UG.bc (inclR (F := F) R) γ ∈ HR R σ J := by
  have h0 : Formalism.UG.cT (σ : E →+* E) γ.1 * J * γ.1 = J := h
  have h3 : (Formalism.UG.cT (σ : E →+* E) γ.1).map (inclR (F := F) R) =
      Formalism.UG.cT (sigR R σ) (γ.1.map (inclR (F := F) R)) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR]
  have h4 := congrArg (fun m => m.map (inclR (F := F) R)) h0
  simp only [Matrix.map_mul, h3] at h4
  exact h4

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genus_exists_rat (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E)
    (h : ∀ u v, herm (-V.gram.transpose) (γ.1 *ᵥ u) (γ.1 *ᵥ v) = herm (-V.gram.transpose) u v) :
    ∃ γ' ∈ GQ V, (finHom V γ').1 = γ.1.map (inclR (F := D.host.F) (Af D.host.F)) := by
  have h1 := genus_mem_UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (fun _ => rfl) V.gram γ h
  refine ⟨(⟨_, genus_bc_mem_HR (AF D.host.F) D.sp.cm.sig V.gram γ h1⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram),
    ⟨γ, h1, rfl⟩, ?_⟩
  ext i j
  rfl

theorem genus_mulVec_inj {A : Type} [CommRing A] {n : ℕ} (g : GL (Fin n) A) {u v : Fin n → A}
    (h : g.1 *ᵥ u = g.1 *ᵥ v) : u = v := by
  have := congrArg (fun t => (g⁻¹).1 *ᵥ t) h
  simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using this

theorem genus_sub_eq {A : Type} [AddCommGroup A] (N : ℕ) (x e y w : A) (h : y + N • w = x + N • e) :
    x - y = N • (w - e) := by
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← h, add_comm]

set_option maxHeartbeats 800000 in

theorem genus_marked (hH : GlobalTheory.Published.HasseNormSt) (D : D7) (V : HSp D)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (hA : l.A = 1) (hσ : σ' (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H Dw.p Dw.q ty) {r : ℕ} (hr : V.rank = r) (M : GlobalTheory.FrameUnif.ModelsOf F r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) (h : GA D V) :
    ∃ p, MarkSpec M V hr io th x₀ h p := by
  subst hr
  obtain ⟨hbase, hW, ⟨hinj, hrange⟩, hEF, -, -⟩ := hR
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  let X0 := M.X ⟨0, F.n_pos⟩
  have hGm : X0.Gm = -V.gram.transpose := (hW _).1
  have hξ0 : X0.ξ0 = -D.host.xi0 := (hW _).2
  have hξ : -(-D.host.xi0) ≠ 0 := by
    rw [← hξ0]
    exact neg_ne_zero.2 X0.ξ0_ne
  have hξ' : cc (-(-D.host.xi0)) = -(-(-D.host.xi0)) := by
    have h := X0.ξ0_im
    rw [hξ0] at h
    unfold cc at h ⊢
    rw [map_neg, h]
  have hφ : Function.Injective io ∧ Submodule.span D.host.E (Set.range io) = ⊤ ∧
      (∀ a b, cc ((-V.gram.transpose) a b) = (-V.gram.transpose) b a) ∧ (-V.gram.transpose).det ≠ 0 ∧
      ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
        (-(-D.host.xi0) * herm (-V.gram.transpose) (io x) (io y)) :=
    ⟨hinj, hsp, hGm ▸ X0.Gm_herm, hGm ▸ X0.Gm_det, hEF⟩
  have hsd := (GlobalTheory.HermModel.rank_integral_selfDual _ H Dw V.rank _ _ io hξ' hφ).2.2.2
  have hu : ∀ x y, AdLat.hermA (LevelHalf.conjEquiv D.sp.cm) (-V.gram.transpose) ((finHom V h).1 *ᵥ x)
      ((finHom V h).1 *ᵥ y) = AdLat.hermA (LevelHalf.conjEquiv D.sp.cm) (-V.gram.transpose) x y := by
    intro x y
    have := LevelHalf.hermA_unitary D.sp.cm V.gram _ (LevelHalf.finHom_mem V h) x y
    simp only [AdLat.hermA, Matrix.neg_apply, TensorProduct.tmul_neg, mul_neg, neg_mul, Finset.sum_neg_distrib,
      neg_inj] at this ⊢
    exact this
  obtain ⟨hΛfg, hΛsp, hΛsd, f, hf1, hf2, hf3, hf4⟩ := genus_translate D.host.F D.host.E V.rank
    (LevelHalf.conjEquiv D.sp.cm) (fun _ => rfl) (-V.gram.transpose) hφ.2.2.1 hφ.2.2.2.1 _ hξ
    (LinearMap.range io) (latG V h) hfg hsp
    (fun v => by
      rw [← hsd v]
      exact ⟨fun hv y => hv _ ⟨y, rfl⟩, by rintro hv _ ⟨y, rfl⟩; exact hv y⟩)
    (finHom V h) hu (hlat h).1
  let ψ : Dw.La ≃ₗ[𝓞 D.host.E] LinearMap.range io := LinearEquiv.ofInjective io hinj
  obtain ⟨k, γ, hγ1, hγ2, hγ3⟩ := GlobalTheory.selfDual_lattice_occurs hH _ H Dw l Xo σ' g ty F V.rank M (-D.host.xi0)
    (-V.gram.transpose) io (latG V h) (fun N => f N ∘ₗ ψ.toLinearMap) hA hσ hty hbase hW hφ hΛfg hΛsp hΛsd
    (fun N m hN hm a => hf2 N m hN hm (ψ a))
    (fun N hN => ⟨fun a => ((hf3 N hN).1 (ψ a)).trans
        ⟨fun ⟨v, hv⟩ => ⟨ψ.symm v, ψ.injective (by rw [hv, map_nsmul, LinearEquiv.apply_symm_apply])⟩,
          fun ⟨v, hv⟩ => ⟨ψ v, by rw [hv, map_nsmul]⟩⟩,
      fun a' => by
        obtain ⟨a, v, hv⟩ := (hf3 N hN).2 a'
        obtain ⟨a, rfl⟩ := ψ.surjective a
        exact ⟨a, v, hv⟩⟩)
    (fun N hN a a' => by
      obtain ⟨z, hz⟩ := hf4 N hN (ψ a) (ψ a')
      exact ⟨z, by rw [hφ.2.2.2.2]; exact hz⟩)
  obtain ⟨γ', hγ', hfin⟩ := genus_exists_rat D V γ hγ1
  have hmul : ∀ z, (finHom V (γ' * h)).1 *ᵥ z =
      γ.1.map (inclR (F := D.host.F) (Af D.host.F)) *ᵥ ((finHom V h).1 *ᵥ z) := fun z => by
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hfin]
  have hΛ : ∀ v, v ∈ (M.X k).Λ ↔ v ∈ AdLat.latOf D.host.F (finHom V (γ' * h)).1 (LinearMap.range io) := by
    intro v
    obtain ⟨v, rfl⟩ : ∃ u, γ.1 *ᵥ u = v :=
      ⟨(γ⁻¹).1 *ᵥ v, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
    rw [← hγ2, ← SetLike.mem_coe, (hlat h).1]
    refine exists_congr fun z => and_congr_right fun _ => ?_
    rw [hmul, genus_fv_mulVec, ← hfin]
    refine ⟨fun e => by rw [e], fun e => ?_⟩
    exact genus_mulVec_inj (finHom V γ') e
  refine ⟨⟨k, fun τ => (Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) (γ' * h)) * x₀ τ.1 :
    Matrix (Fin V.rank) (Fin V.rank) ℂ)⟩, γ', hγ', ?_, fun a ha => ?_, fun τ => rfl⟩
  · rw [(hlat _).1]
    refine Eq.trans ?_ (Set.image_id _).symm
    ext v
    exact hΛ v
  · obtain ⟨w, hw, e⟩ := hγ3 a ha
    obtain ⟨w', hw', e'⟩ := hf1 l.M (lt_of_lt_of_le (by norm_num) l.three_le) (ψ a)
    have m1 : AdLat.fv D.host.F w ∈ latGHat V (γ' * h) := by
      rw [← SetLike.mem_coe, (hlat _).2]
      exact (hΛ w).1 hw
    have m2 : (finHom V (γ' * h)).1 *ᵥ w' ∈ latGHat V (γ' * h) := by
      rw [← SetLike.mem_coe, (hlat _).2]
      exact ⟨w', hw', rfl⟩
    refine ⟨_, sub_mem m2 m1, ?_⟩
    change AdLat.fv D.host.F (M.φ k (F.t k a) : Fin V.rank → D.host.E) -
      (finHom V (γ' * h)).1 *ᵥ AdLat.fv D.host.F (io a) = _
    apply genus_sub_eq
    rw [← AdLat.Tower.mulVec_nsmul, ← Matrix.mulVec_add, hmul, ← AdLat.Tower.fv_nsmul, ← AdLat.Tower.fv_add, ← e,
      genus_fv_mulVec]
    exact congrArg _ e'.symm

theorem exists_markSpec : GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ h : GA D (D.sp.W j), ∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p :=
  fun hH D Q hQ j hj _ _ _ F hσ hty M io th x₀ hR h =>
    genus_marked hH D (D.sp.W j) F (level_good_and_sign D Q hQ).2.1 hσ hty (D.sp.W_rank j hj.1 hj.2) M io th x₀ hR h

end GlobalTheory.RecDict
