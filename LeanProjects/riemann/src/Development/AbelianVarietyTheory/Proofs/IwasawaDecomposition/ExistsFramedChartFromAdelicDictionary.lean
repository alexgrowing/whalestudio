import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedPointClassesBijectiveDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecorated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelSmallerAtFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QbKLeLocLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabIffMemConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAboveStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem localComponent_congr {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} (hP : P.under (𝓞 F) = v)
    {x x' : GL (Fin n) (AfE F E)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') : rhoP F P x = rhoP F P x' := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h0 : prV (E := E) v ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j) = prV (E := E) v ((x' : Matrix (Fin n) (Fin n) (AfE F E)) i j) :=
    congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h
  have h1 : prV (E := E) v ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j - (x' : Matrix (Fin n) (Fin n) (AfE F E)) i j) = 0 := by
    rw [map_sub, h0, sub_self]
  have h2 := (GlobalTheory.T.placeProjection_zero_integral_iff_components_above F E v _).1.1 h1 P hP
  rw [map_sub, sub_eq_zero] at h2
  exact h2

end SlopeTestRemainingChoices

section Dense

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  {hc : CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem valuation_entries_le_one_of_mem_levelGroupOne {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG) (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    Valued.v (adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
  obtain ⟨y, hy, -⟩ := St_one_int (congruence_subgroup_le_stabilizer hc n ST (principal_le_congruence_subgroup hc n ST SG hz))
  rw [hy]
  exact (mem_rInt_iff F E _).1 (y i j).2 P

theorem rhoP_mem_qbK {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG) (P : HeightOneSpectrum (𝓞 E)) {c : E} (h0 : c ≠ 0)
    (hs : Sm Valued.v (P.valuation E c) (locM P z - 1)) : rhoP F P z ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hc0 : algebraMap E (P.adicCompletion E) c ≠ 0 := by
    simpa using h0
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · exact valuation_entries_le_one_of_mem_levelGroupOne hz P i j
  · rw [← map_inv]
    exact valuation_entries_le_one_of_mem_levelGroupOne (inv_mem hz) P i j
  · refine ⟨(locM P z - 1) i j / algebraMap E (P.adicCompletion E) c, ?_, ?_⟩
    · show Valued.v ((locM P z - 1) i j / algebraMap E (P.adicCompletion E) c) ≤ 1
      rw [map_div₀, valued_algebraMap]
      exact div_le_one_of_le₀ (hs i j) zero_le'
    · rw [mul_div_cancel₀ _ hc0]
      rfl

theorem topU_dense {U : Subgroup (GL (Fin n) (AfE F E))} {Λ : LevFam E K n SG} {Θ : LevQFam E K n Q} {d : Q → E} {k t : GL (Fin n) (AfE F E)}
    (e : ℕ) (hd : ∀ P, d P ≠ 0) (hQ : ∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q)
    (hdq : ∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) (hk : k ∈ UAd hc n) (hrk : ∀ P : Q, rhoP F P.1 k = 1) (ht : t ∈ K1 hc n ST SG)
    (hU : ∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) :
    ∀ g ∈ UAd hc n, ∃ x ∈ topU U t Θ d, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * (k * t)) p := by
  intro g hg
  have hkt : k * t ∈ UAd hc n := mul_mem hk (principal_le_adelic_unitary hc n ST SG ht)
  obtain ⟨z, hz, hsm, p, hp⟩ := GlobalTheory.T.exists_K1_point_congruent F E hc n ST SG Q hQ (g * (k * t)) (mul_mem hg hkt) e
  have hzU := principal_le_adelic_unitary hc n ST SG hz
  refine ⟨(k * t) * z * (k * t)⁻¹, ⟨?_, ?_⟩, p, ?_⟩
  · refine (hU _ (mul_mem (mul_mem hkt hzU) (inv_mem hkt))).2 ?_
    have e1 : k⁻¹ * ((k * t) * z * (k * t)⁻¹) * k = t * z * t⁻¹ := by group
    rw [e1]
    have hle := kOne_le_unipotentLevel hc n ST SG Λ.grp
    exact mul_mem (mul_mem (hle ht) (hle hz)) (inv_mem (hle ht))
  · refine Subgroup.mem_iInf.2 fun P => ?_
    have e2 : rhoT F P.1 t ((k * t) * z * (k * t)⁻¹) = rhoP F P.1 z := by
      have e3 : t⁻¹ * ((k * t) * z * (k * t)⁻¹) * t⁻¹⁻¹ = t⁻¹ * k * t * z * t⁻¹ * k⁻¹ * t := by group
      show rhoP F P.1 (t⁻¹ * ((k * t) * z * (k * t)⁻¹) * t⁻¹⁻¹) = _
      rw [e3]
      simp only [map_mul, map_inv, hrk P, inv_one, mul_one, inv_mul_cancel, one_mul, mul_inv_cancel_right]
      group
    refine Subgroup.mem_comap.2 ?_
    rw [e2]
    refine qbK_le_locLev P.1 (Θ P) (d P) (rhoP_mem_qbK hz P.1 (hd P) ?_)
    rw [hdq P]
    exact hsm P
  · have e4 : g * ((k * t) * z * (k * t)⁻¹) * (k * t) = g * (k * t) * z := by group
    rw [e4]
    exact hp

end Dense

set_option maxHeartbeats 1000000 in

theorem exists_clsG_top : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E hc.sig J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (e : ℕ) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (k t : GL (Fin n) (AfE F E)) (C : Type) (s : C → DecoF E n ST SG Q) (y : C → GL (Fin n) (AfE F E)) (stab : C → Type) [∀ c, Group (stab c)] (lat : C → Submodule (𝓞 E) (Fin n → E)) (gm : ∀ c, stab c →* UF E n) (ψ : topU S.U t Θ d →* ℂˣ), J = 1 → (∀ v, v ∈ Qv ↔ ∃ P ∈ Q, P.under (𝓞 F) = v) → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → (∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) → k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ S.U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → (∀ c, IsPtOf hc (y c * (k * t)) (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = p) → (∀ c, lat c = (s c).deco.1.L) → (∀ c, Function.Injective (gm c)) → (∀ c (γ : UF E n), γ ∈ (gm c).range ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = s c) → (∀ x : topU S.U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → ψ x = 1) → ∃ C' : ClsG hc.sig J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) stab lat, C'.lev.Lb = S.Lb ∧ C'.lev.U = topU S.U t Θ d ∧ (∀ v, v ∉ Qv → C'.lev.Uloc v = S.Uloc v) ∧ (∀ (x : C'.lev.U) (x' : S.U) (x'' : topU S.U t Θ d), x.1 = x'.1 → x.1 = x''.1 → C'.lev.chi x = S.chi x' * ψ x'') ∧ (∀ c, (C'.y c).1 = y c) ∧ ∀ c s, (C'.stabI c s).1 = ufGL E n (gm c s) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q J T f bad S Qv Λ Θ e d hd N hdN hΘ k t C s y stab _ lat gm ψ
    hJ hQv hT hQ hdq hk hrk ht hU hlatS hpt hinj hsurj hlatc hgmi hgr hψ
  subst hJ
  have hkt : k * t ∈ UAd hc n := mul_mem hk (principal_le_adelic_unitary hc n ST SG ht)
  have hover : ∀ P : Q, P.1.under (𝓞 F) ∈ Qv := fun P => (hQv _).2 ⟨P.1, P.2, rfl⟩
  have hloc : ∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ topU S.U t Θ d, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ topU S.U t Θ d := by
    intro x hx h
    refine ⟨hx, Subgroup.mem_iInf.2 fun P => ?_⟩
    obtain ⟨x', hx', e'⟩ := h _ (hover P)
    have e1 : rhoT F P.1 t x = rhoT F P.1 t x' := by
      show rhoP F P.1 (t⁻¹ * x * t⁻¹⁻¹) = rhoP F P.1 (t⁻¹ * x' * t⁻¹⁻¹)
      have e0 := localComponent_congr (P := P.1) rfl e'
      simp only [map_mul, e0]
    refine Subgroup.mem_comap.2 ?_
    rw [e1]
    exact rhoT_mem hx' P
  have hψ' : ∀ x : topU S.U t Θ d, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1 := fun x h => hψ x fun P => by
    have h1 := localComponent_congr (P := P.1) rfl ((h _ (hover P)).trans (map_one (bc (prV (E := E) (P.1.under (𝓞 F))))).symm)
    rw [h1, map_one]
  obtain ⟨L, hLb, hLU, hLoc, hLchi⟩ := GlobalTheory.T.exists_stepLevel_smaller_at_finite_places F E hc.sig n 1 T f bad S Qv (topU S.U t Θ d) ψ (topU_le _ _ _ _) hT hloc
    (topU_open F E K hc.sig n 1 Q S.U t Θ d hd S.U_open) hψ'
  have hyU : ∀ c, y c ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) := fun c => by
    have h1 : y c * (k * t) * (k * t)⁻¹ ∈ UAd hc n := mul_mem (hpt c).uni (inv_mem hkt)
    rwa [mul_inv_cancel_right] at h1
  have hlev : ∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * (k * t)) p → IsPtOf hc (g * x * (k * t)) p' →
      (x ∈ topU S.U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p = p') :=
    fun g x p p' h h' => GlobalTheory.T.mem_framedLevel_iff_two_adelic_points F E K hc n ST SG Q Λ Θ d hd N hdN hΘ S.U k t g x p p' hk hrk ht hU h h'
  have hle : topU S.U t Θ d ≤ UAd hc n := fun x hx => ((S.U_eq x).1 (topU_le _ _ _ _ hx)).1
  let sI : ∀ c, stab c →* UJ (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) := fun c =>
    ((ufGL E n).comp (gm c)).codRestrict _ fun a => by
      show ufGL E n (gm c a) ∈ URat hc n
      rw [RatMove.ufGL_eq hc]
      exact ((ratEquiv hc n).symm (gm c a)).2
  refine ⟨{ lev := L, y := fun c => ⟨y c, hyU c⟩, y_bij := ?_, y_lat := ?_, stabI := sI, stabI_inj := ?_, stabI_range := ?_ },
    hLb, hLU, hLoc, hLchi, fun c => rfl, fun c a => rfl⟩
  · refine GlobalTheory.T.decoratedPointClasses_bijective_doubleCosets F E K hc n ST SG Q C Λ Θ s L.U (k * t) (fun c => ⟨y c, hyU c⟩) (hLU ▸ hle) hkt ?_ ?_ hpt hinj hsurj
    · rw [hLU]; exact hlev
    · rw [hLU]; exact topU_dense e hd hQ hdq hk hrk ht hU
  · intro c x
    rw [hlatc c, hLb]
    exact PtLat.latS_deco_iff F E hc n ST SG Q S.Lb k t (y c) (s c) ht hlatS (hpt c) x
  · intro c a b h
    have h1 : ufGL E n (gm c a) = ufGL E n (gm c b) := congrArg Subtype.val h
    exact hgmi c (Subtype.ext ((toGLm E n).injective h1))
  · intro c γ
    have e1 : ufGL E n (ratHom hc n γ) = γ.1 := by
      rw [RatMove.ufGL_eq hc]
      exact congrArg Subtype.val ((ratEquiv hc n).symm_apply_apply γ)
    have key := stab_iff_mem_conj F E K hc n ST SG Q Λ Θ (topU S.U t Θ d) (k * t) (y c) (s c) hlev (hpt c) (ratHom hc n γ)
    have e2 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 = ratAd F (ratHom hc n γ) := by rw [ratAd, e1]
    rw [e2, hLU]
    refine Iff.trans ?_ ((hgr c _).trans key)
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, Subtype.ext ((toGLm E n).injective ?_)⟩
      exact (congrArg Subtype.val ha).trans e1.symm
    · rintro ⟨a, ha⟩
      refine ⟨a, Subtype.ext ?_⟩
      show ufGL E n (gm c a) = γ.1
      rw [ha, e1]

end GlobalTheory.Mem.Col2.TopCh

end
