import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefined
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldCurveStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.DetFibre

theorem exists_complete_of_idem {R ι A : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (a₀ : A) (χ : ι → R) (hχ : ∀ i, χ i * χ i = χ i) (t : ι → A) :
    ∃ cs : A → R, (∀ a, cs a * cs a = cs a) ∧ (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
      (∀ S : Subring R, (∀ i, χ i ∈ S) → ∀ a, cs a ∈ S) ∧
      ∀ (T : Type) [CommRing T] (φ : R →+* T) (i : ι), (∀ j, φ (χ j) = if i = j then 1 else 0) →
        ∀ a, φ (cs a) = if t i = a then 1 else 0 := by
  let e : A → R := fun a => ∏ i, if t i = a then 1 else 1 - χ i
  let z : R := ∏ i, (1 - χ i)
  have h1 : ∀ i, (1 - χ i) * (1 - χ i) = 1 - χ i := fun i => by linear_combination hχ i
  have ee : ∀ a, e a * e a = e a := fun a => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · exact one_mul _
    · exact h1 i
  have ez : ∀ a, e a * z = z := fun a => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · exact one_mul _
    · exact h1 i
  have zz : z * z = z := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => h1 i
  have eb : ∀ a b, a ≠ b → e a * e b = z := fun a b hab => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with ha hb
    · exact absurd (ha.symm.trans hb) hab
    · exact one_mul _
    · exact mul_one _
    · exact h1 i
  let f : A → R := fun a => e a - z
  have ff : ∀ a, f a * f a = f a := fun a => by
    simp only [f]; linear_combination ee a - 2 * ez a + zz
  have fb : ∀ a b, a ≠ b → f a * f b = 0 := fun a b hab => by
    simp only [f]; linear_combination eb a b hab - ez a - ez b + zz
  let s : R := ∑ a, f a
  have fs : ∀ a, f a * s = f a := fun a => by
    rw [Finset.mul_sum, Finset.sum_eq_single a (fun b _ hb => fb a b hb.symm) (by simp), ff]
  have ss : s * s = s := by
    conv_lhs => rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => fs a
  refine ⟨fun a => f a + if a = a₀ then 1 - s else 0, fun a => ?_, fun a b hab => ?_, ?_, fun S hS a => ?_,
    fun T _ φ i hφ a => ?_⟩
  · beta_reduce
    split_ifs
    · linear_combination ff a - 2 * fs a + ss
    · simp [ff]
  · beta_reduce
    split_ifs with ha hb
    · exact absurd (ha.trans hb.symm) hab
    · linear_combination fb a b hab - fs b
    · linear_combination fb a b hab - fs a
    · simp [fb a b hab]
  · rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [s]
  · have hf : ∀ a, f a ∈ S := fun a => by
      refine sub_mem (prod_mem fun i _ => ?_) (prod_mem fun i _ => sub_mem (one_mem _) (hS i))
      split_ifs
      · exact one_mem _
      · exact sub_mem (one_mem _) (hS i)
    refine add_mem (hf a) ?_
    split_ifs
    · exact sub_mem (one_mem _) (sum_mem fun a _ => hf a)
    · exact zero_mem _
  · have hz : φ z = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hφ])
    have hf : ∀ a, φ (f a) = if t i = a then 1 else 0 := fun a => by
      rw [map_sub, hz, sub_zero, map_prod]
      split_ifs with h
      · refine Finset.prod_eq_one fun j _ => ?_
        split_ifs with h'
        · exact map_one _
        · have : i ≠ j := fun hij => h' (hij ▸ h)
          simp [hφ, this]
      · exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hφ, h])
    have hs : φ s = 1 := by
      rw [map_sum, Finset.sum_congr rfl fun a _ => hf a, Finset.sum_ite_eq]
      simp
    rw [map_add, hf]
    split_ifs <;> simp [hs]

section Periods

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_idem_of_map (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (hcl : FnAlgClosed Xo c)
    {A : Type} [Fintype A] [DecidableEq A] (a₀ : A) (t : Fin F.n → A) :
    ∃ cs : A → Rul Xo c, (∀ a, cs a ∈ sec Xo c 0 0) ∧ (∀ a, cs a * cs a = cs a) ∧
      (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
      ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P, IsPeriod (F.Di i) ty P → y.x = F.u i P →
        ∀ a, Formalism.L2.PjFree.toC (evR Xo c (cs a) y) = if t i = a then 1 else 0 := by
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.allSixLaws.1.secBaseChange E H Dw l Xo c
  choose χ h1 h2 h3 using GlobalTheory.CompFun.exists_idempotent hA σ F hcl
  obtain ⟨cs, k1, k2, k3, k4, k5⟩ := exists_complete_of_idem a₀ χ h2 t
  let S : Subring (Rul Xo c) :=
    { (sec Xo c 0 0).toAddSubgroup with
      one_mem' := GlobalTheory.CompFun.one_mem_sec
      mul_mem' := fun ha hb => by simpa using sec_mul Xo c 0 0 0 0 ha hb }
  refine ⟨cs, k4 S h1, k1, k2, k3, fun y i P hP hy a => ?_⟩
  have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hy' := hA (CAt σ) y
  let ev : Rul Xo c →+* CAt σ :=
    { toFun := fun f => evR Xo c f y
      map_one' := evalAt_one _ _ y hy'
      map_mul' := fun f f' => evalAt_mul _ _ f f' y
      map_zero' := evalAt_zero _ _ y
      map_add' := fun f f' => evalAt_add _ _ f f' y }
  exact k5 (CAt σ) ev i (fun j => h3 j y i P hP hy) a

end Periods

section Marks

open GlobalTheory.CharRead

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem det_cong_of_finCong (V : HSp D) (N : ℕ) (hN : N ≠ 0) (u : GA D V) (hu : FinCong V N u) :
    ∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (N : ℕ) • w := by
  obtain ⟨k1, -, k3, k4, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  exact det_cong_one D.host.F (latC V) k3 k4 N hN (finHom V u).1 (by rw [← k1]; exact hu)

set_option maxHeartbeats 800000 in

theorem exists_rat_of_marks (l : Level H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (t : Dw.La → La)
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : La ≃ₗ[𝓞 D.host.E] Λ) (φ' : La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (t a) : Fin V.rank → D.host.E) - (finHom V g).1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (t a) : Fin V.rank → D.host.E) - (finHom V g').1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hΛ hΛ'
  obtain ⟨r1, -, r3, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := exists_unitary_of_trace_eq _ _ (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.1 (GlobalTheory.T.adelicElementLattice_full_and_completion D V g').2.1
    φ φ' _ ξ hξ htr
  obtain ⟨γ, hγ⟩ := r3 δ hδ3
  obtain ⟨m1, m2⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ δ g hγ
  have hlat : latG V (γ * g) = latG V g' := by
    ext v
    have hv : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
        (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have a1 := m1 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    have a2 := hδ2 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    rw [hv] at a1 a2
    exact a1.symm.trans a2
  have hc : FinCong V l.M ((γ * g)⁻¹ * g') := by
    refine finCong_of_marks l V io hio _ _ hlat (fun a => finVec V (φ' (t a) : Fin V.rank → D.host.E)) ?_ hM'
    intro a ha
    obtain ⟨w, hw, e⟩ := hM a ha
    refine ⟨_, (m2 w).1 hw, ?_⟩
    have e2 := congrArg (fun z => (finHom V γ).1 *ᵥ z) e
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
    rw [(r5 _ δ hγ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hδ1] at e2
    exact e2
  have hu : gLat V ((γ * g)⁻¹ * g') = latHat V := by
    refine gLat_eq_of_finCong V _ ((GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat) ?_
    have e0 : ((γ * g)⁻¹ * g')⁻¹ = g'⁻¹ * (γ * g) := by group
    rw [e0]
    exact (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat.symm
  exact ⟨γ, (r1 γ).2 ⟨δ, hγ⟩, _, hu, hc, (mul_inv_cancel_left _ _).symm⟩

theorem exists_rat_of_index {l : Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {n : ℕ} {ty : Fin n → D.host.E →+* ℂ}
    (F : FamilyUnif Xo s ty) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) (i i' : Fin F.n) (hi : i = i')
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] Λ) (φ' : (F.Di i').La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)))
    (htr' : ∀ a b, (((F.Di i').EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (F.t i a) : Fin V.rank → D.host.E) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (F.t i' a) : Fin V.rank → D.host.E) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hi
  exact exists_rat_of_marks l V io hio (F.t i) g g' Λ Λ' hΛ hΛ' φ φ' ξ hξ
    (fun a b => (htr a b).symm.trans (htr' a b)) hM hM'

set_option maxHeartbeats 1000000 in

theorem exists_map_of_invariant {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (σ : c.F →+* ℂ) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hio : LatEmb V io) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    {A : Type} (ν : GA D V → A) (h1 : ∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, ν (h * u) = ν h)
    (h2 : ∀ γ ∈ GQ V, ∀ h, ν (γ * h) = ν h) :
    ∃ t : Fin F.n → A, (∀ i, ∃ h, t i = ν h) ∧
      ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → t (ik (dict h).1) = ν (γ * h) := by
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h γ h' γ', MarkBy U V rfl dict io F ik φ h γ → MarkBy U V rfl dict io F ik φ h' γ' →
      ik (dict h).1 = ik (dict h').1 → ν (γ * h) = ν (γ' * h') := by
    intro h γ h' γ' hm hm' hi
    have hξ : -(-D.host.xi0) ≠ 0 := by
      rw [← (hW (dict h).1).2]
      exact neg_ne_zero.2 (U.X _).ξ0_ne
    obtain ⟨δ, hδ, u, hu1, hu2, hu3⟩ := exists_rat_of_index F V io hio _ _ hi _ _ _ _
      (SetLike.ext' (hm.2.1.trans (Set.image_id _)))
      (SetLike.ext' (hm'.2.1.trans (Set.image_id _))) (φ _) (φ _) _ hξ (htr _) (htr _) hm.2.2 hm'.2.2
    rw [hu3, h1 u hu1 hu2, h2 δ hδ]
  have hv : ∀ i : Fin F.n, ∃ a : A, (∃ h, a = ν h) ∧
      ∀ h γ, MarkBy U V rfl dict io F ik φ h γ → ik (dict h).1 = i → a = ν (γ * h) := by
    intro i
    by_cases hex : ∃ h γ, MarkBy U V rfl dict io F ik φ h γ ∧ ik (dict h).1 = i
    · obtain ⟨h, γ, hm, hi⟩ := hex
      exact ⟨_, ⟨_, rfl⟩, fun h' γ' hm' hi' => key h γ h' γ' hm hm' (hi.trans hi'.symm)⟩
    · exact ⟨_, ⟨1, rfl⟩, fun h γ hm hi => absurd ⟨h, γ, hm, hi⟩ hex⟩
  choose t ht1 ht2 using hv
  exact ⟨t, ht1, fun h γ hm => ht2 _ h γ hm rfl⟩

set_option maxHeartbeats 1000000 in

theorem exists_idem_of_invariant {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (σ : c.F →+* ℂ) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hio : LatEmb V io) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (hcl : FnAlgClosed Xo c)
    {A : Type} [Fintype A] [DecidableEq A] (ν : GA D V → A)
    (h1 : ∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, ν (h * u) = ν h)
    (h2 : ∀ γ ∈ GQ V, ∀ h, ν (γ * h) = ν h) :
    ∃ cs : A → Rul Xo c, (∀ a, cs a ∈ sec Xo c 0 0) ∧ (∀ a, cs a * cs a = cs a) ∧
      (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
      ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → ∀ a,
        rdU U (cs a) (dict h).1 (dict h).2 = (if ν (γ * h) = a then 1 else 0) ∧
        ∀ (y : FrPt Xo c (CAt σ)) P, IsPeriod (F.Di (ik (dict h).1)) (fun j => relab c σ (e j).1) P →
          y.x = F.u (ik (dict h).1) P → toC (evR Xo c (cs a) y) = if ν (γ * h) = a then 1 else 0 := by
  obtain ⟨t, -, ht⟩ := exists_map_of_invariant V io σ r hr U dict g e F ik φ th x₀ hio hW hD ν h1 h2
  obtain ⟨cs, k0, k1, k2, k3, k4⟩ := exists_idem_of_map σ F hcl (ν 1) t
  refine ⟨cs, k0, k1, k2, k3, fun h γ hm a => ⟨?_, fun y P hP hy => ?_⟩⟩
  · obtain ⟨Pm, -, hP, hx, -⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hdom h⟩
    rw [← ht h γ hm, ← k4 _ _ Pm hP hx a]
    exact dif_pos (hdom h)
  · rw [← ht h γ hm, ← k4 y _ P hP hy a]
    rfl

set_option maxHeartbeats 1000000 in

theorem exists_idem_rdU_det {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (σ : c.F →+* ℂ) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hio : LatEmb V io) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (hcl : FnAlgClosed Xo c)
    {A : Type} [Fintype A] [DecidableEq A] (ν : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ → A)
    (h1 : ∀ u : GA D V, gLat V u = latHat V →
      (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) →
      ∀ h, ν (Matrix.GeneralLinearGroup.det (finHom V (h * u))) = ν (Matrix.GeneralLinearGroup.det (finHom V h)))
    (h2 : ∀ γ ∈ GQ V, ∀ h,
      ν (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) = ν (Matrix.GeneralLinearGroup.det (finHom V h))) :
    ∃ cs : A → Rul Xo c, (∀ a, cs a ∈ sec Xo c 0 0) ∧ (∀ a, cs a * cs a = cs a) ∧
      (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
      ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → ∀ a,
        rdU U (cs a) (dict h).1 (dict h).2 =
          if ν (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) = a then 1 else 0 := by
  obtain ⟨cs, k0, k1, k2, k3, k4⟩ := exists_idem_of_invariant V io σ r hr U dict g e F ik φ th x₀ hio hW hD hdom hcl
    (fun h => ν (Matrix.GeneralLinearGroup.det (finHom V h)))
    (fun u hu hc => h1 u hu (det_cong_of_finCong V l.M (by have := l.three_le; omega) u hc)) h2
  exact ⟨cs, k0, k1, k2, k3, fun h γ hm a => (k4 h γ hm a).1⟩

theorem hom_invariant {G A : Type} [Group G] [Group A] (κ : G →* A) {u : G} (hu : κ u = 1) (h : G) :
    κ (h * u) = κ h ∧ κ (u * h) = κ h := by
  simp [hu]

theorem idem_mul_pow_succ {R : Type} [CommRing R] {s f : R} {m : ℕ} (hs : s * s = s) (hf : f ^ m = 1) :
    (s * f) ^ (m + 1) = s * f := by
  rw [mul_pow, IsIdempotentElem.pow_succ_eq m hs, pow_succ, hf, one_mul]

theorem fnAlgClosed_of_iotaOK {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : IotaOK Dw V io) (hpos : 1 ≤ Dw.p + Dw.q)
    (hrk : Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hc : CurveOver H c.F l.M) : FnAlgClosed Xo c :=
  GlobalTheory.CompRat.fnAlgClosed_of_curveOver _ H Dw l Xo c hpos hA
    (hrk.imp_right (Or.imp_right fun h => ⟨h, GlobalTheory.RankOneDatum.exists_datum_rank_one D H Dw V io hio hpos⟩)) hc

end Marks

set_option maxHeartbeats 1000000 in

theorem exists_unramified_field_fibres (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l l₂ : Level H) (c : Coeff l)
    (n p : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ n) (hMn : Nat.Coprime l.M n) (hM : l₂.M = l.M * n) (hA : l₂.A = 1)
    (hgood : l.GoodAt p) (hcurve : CurveOver H c.F l.M) :
    ∃ (c₁ : Coeff l) (c₂ : Coeff l₂), c₂.F = c₁.F ∧ c.F ≤ c₂.F ∧ CurveOver H c₂.F l₂.M ∧
    (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → (∀ x ∈ c₂.F, τ x ∈ c₂.F) ∧
      ∀ O : ValuationSubring ℂ, (p : ℂ) ∈ O.nonunits → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ O → τ x - x ∈ O.nonunits) →
        ∀ x ∈ c₂.F, τ x = x) ∧
    ∀ (Dw : Datum H) (Xo₂ : Moduli Dw l₂) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)),
    IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) →
    FnAlgClosed Xo₂ c₂ ∧ ∀ (σ : c₂.F →+* ℂ) (r : ℕ) (hr : V.rank = r) (U : Unf Xo₂ c₂ σ r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo₂ (σ.comp (IntermediateField.inclusion c₂.le).toRingHom) (fun j => relab c₂ σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
    GoodEmb c₂ σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ →
    (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) →
    (∀ (A : Type) [Fintype A] [DecidableEq A] (ν : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ → A),
      (∀ u : GA D V, gLat V u = latHat V →
        (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l₂.M : ℕ) • w) →
        ∀ h, ν (Matrix.GeneralLinearGroup.det (finHom V (h * u))) = ν (Matrix.GeneralLinearGroup.det (finHom V h))) →
      (∀ γ ∈ GQ V, ∀ h,
        ν (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) = ν (Matrix.GeneralLinearGroup.det (finHom V h))) →
      ∃ cs : A → Rul Xo₂ c₂, (∀ a, cs a ∈ sec Xo₂ c₂ 0 0) ∧ (∀ a, cs a * cs a = cs a) ∧
        (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
        ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → ∀ a,
          rdU U (cs a) (dict h).1 (dict h).2 =
            if ν (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) = a then 1 else 0) ∧
    ∀ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ,
      (∀ u : GA D V, gLat V u = latHat V →
        (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l₂.M : ℕ) • w) →
        xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1) →
      (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1) →
      (∀ h : GA D V, ∃ a : c₂.F, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ)) →
      ∃ f ∈ sec Xo₂ c₂ 0 0,
        (∀ m : ℕ, (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ m = 1) → f ^ m = 1) ∧
        ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ →
          rdU U f (dict h).1 (dict h).2 = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
  obtain ⟨c₂, hle, hc₂, hun⟩ := GlobalTheory.T.exists_coeff_field_curve _ H l l₂ c n p hp hpn hMn hM hA hgood hcurve
  refine ⟨⟨c₂.F, c₂.fin, c₂.conj, hle c.zeta_mem, c.le.trans hle⟩, c₂, rfl, hle, hc₂, hun, ?_⟩
  intro Dw Xo₂ V io hio hpos hrk
  have hcl := fnAlgClosed_of_iotaOK Xo₂ c₂ V io hio hpos hrk hA hc₂
  refine ⟨hcl, fun σ r hr U dict g e F ik φ th x₀ hσ hW hD hdom => ⟨fun A _ _ ν h1 h2 => ?_, ?_⟩⟩
  · exact exists_idem_rdU_det V io σ r hr U dict g e F ik φ th x₀ hio.emb hW hD hdom hcl ν h1 h2
  · exact GlobalTheory.CharRead.exists_sec_rdU_eq_char D H Dw l₂ Xo₂ c₂ σ V r hr U dict io g e F ik φ th x₀ hio hpos hA hσ hW hD
      hdom hcl

end GlobalTheory.DetFibre
