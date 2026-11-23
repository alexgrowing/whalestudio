import Formalism.LocalToGlobal.Columns.TwQTop
import Formalism.LocalToGlobal.Columns.MemLocPOfSmul

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

theorem qdf_frExists : FrExists (n := n) ST SG Q := fun d P => DetChrL.frame_exists P.1 d.2.lat

abbrev qPi (q : QLoc hc n Q Θ) (P : Q) : E ⊗[F] Formalism.L2.Herm.Af F →+* (qv F P.1).adicCompletion F :=
  ((RingHom.fst _ _).comp (q.sp P).toRingHom).comp (prV (E := E) (qv F P.1))

theorem qdf_at_val (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    ((q.at P x : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) = (x : Matrix (Fin n) (Fin n) _).map (qPi q P) := rfl

theorem qdf_pi_iA (q : QLoc hc n Q Θ) (P : Q) (e : E) : qPi q P (iA F E e) = q.phi P e := rfl

theorem qdf_phi_int (q : QLoc hc n Q Θ) (P : Q) (r : 𝓞 E) : q.phi P (r : E) ∈ (qv F P.1).adicCompletionIntegers F := by
  have h : Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E) ∈ Formalism.BasicNotions.intV E (qv F P.1) :=
    Subring.subset_closure (Or.inl ⟨⟨(r : E), r, rfl⟩, rfl⟩)
  exact ((q.sp_int P _).1 h).1

theorem qdf_pi_int (q : QLoc hc n Q Θ) (P : Q) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E) :
    qPi q P a ∈ (qv F P.1).adicCompletionIntegers F := by
  have hle : Formalism.L2.Herm.intAf F E ≤
      (Formalism.BasicNotions.intV E (qv F P.1)).comap (Formalism.UG.prV (E := E) (qv F P.1)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inl ⟨x, ?_⟩))
      simp [Formalism.UG.prV]
    · have hy : ∀ v, (y : Formalism.L2.Herm.Af F) v ∈ v.adicCompletionIntegers F := y.2
      refine Subring.mem_comap.2 (Subring.subset_closure (Or.inr ⟨⟨(y : Formalism.L2.Herm.Af F) (qv F P.1), hy _⟩, ?_⟩))
      simp [Formalism.UG.prV] <;> rfl
  exact ((q.sp_int P _).1 (hle ha)).1

theorem qdf_phi_unit (q : QLoc hc n Q Θ) (P : Q) {s : 𝓞 E} (hs : s ∉ P.1.asIdeal) :
    q.phi P (s : E) ≠ 0 ∧ (q.phi P (s : E))⁻¹ ∈ (qv F P.1).adicCompletionIntegers F := by
  have h1 : Valued.v (q.phi P (s : E)) ≤ 1 := qdf_phi_int q P s
  have h2 : ¬ Valued.v (q.phi P (s : E)) < 1 := fun h => hs ((q.sp_P P s).1 h)
  have hv : Valued.v (q.phi P (s : E)) = 1 := le_antisymm h1 (not_lt.1 h2)
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, map_zero] at hv
    exact zero_ne_one hv
  · show Valued.v (q.phi P (s : E))⁻¹ ≤ 1
    rw [map_inv₀, hv, inv_one]

theorem qdf_phi_intAt (q : QLoc hc n Q Θ) (P : Q) {a : E} (h : IntAt P.1 a) : q.phi P a ∈ (qv F P.1).adicCompletionIntegers F := by
  obtain ⟨r, s, hs, h⟩ := h
  have hu := qdf_phi_unit q P hs
  have hm : q.phi P (s : E) * q.phi P a = q.phi P (r : E) := by
    rw [← map_mul]
    exact congrArg (q.phi P) h
  have ha : q.phi P a = q.phi P (r : E) * (q.phi P (s : E))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hu.1, mul_comm]
    exact hm
  rw [ha]
  exact mul_mem (qdf_phi_int q P r) hu.2

theorem qdf_gl_inv_val {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (A : GL (Fin n) R) :
    (((bc f A)⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) = ((A⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map f := by
  rw [← map_inv]
  rfl

theorem qdf_frLat (q : QLoc hc n Q Θ) : FrLat ST SG q := by
  intro x p hx P
  have hN : p.deco.1.N = Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n) := by
    rw [← hx, rlc_decoOf_val hc n ST SG x.2]; rfl
  set fr := p.fr P with hfr

  have hfrN : ∀ w ∈ p.deco.1.N, ∀ i, q.phi P ((fr.symm w) i) ∈ (qv F P.1).adicCompletionIntegers F := by
    intro w hw i
    have h1 : fr (fr.symm w) ∈ p.deco.1.at P.1 := by
      rw [LinearEquiv.apply_symm_apply]
      exact (mem_locP P.1 _ w).2 ⟨1, P.1.isPrime.one_notMem, by rw [one_smul]; exact hw⟩
    have h2 : fr.symm w ∈ stdAt E n P.1 := (p.2 P (fr.symm w)).1 h1
    exact qdf_phi_intAt q P ((mem_localization_standardLattice P.1 _).1 h2 i)
  have hFinv : ((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) = bc (q.phi P) (qGL n fr.symm) := by
    rw [← map_inv]; congr 1
  constructor
  ·
    set xm : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := x.1 with hxm
    have key : ∀ z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n)), ∀ i,
        ((((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => qPi q P (z k))) i ∈
          (qv F P.1).adicCompletionIntegers F := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨w, hw, rfl⟩ := hz
        intro i
        rw [hFinv]
        have e1 : ((bc (q.phi P) (qGL n fr.symm) : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => qPi q P (iA F E (w k))) =
            fun k => q.phi P ((fr.symm w) k) := by
          funext k
          rw [← toGLm_mulVec fr.symm w]
          exact (RingHom.map_mulVec (q.phi P) _ w k).symm
        rw [e1]
        exact hfrN w (by rw [hN]; exact hw) i
      | zero =>
        intro i
        have e0 : (fun k => qPi q P ((0 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) k)) = 0 := by funext k; simp
        rw [e0, Matrix.mulVec_zero]
        exact zero_mem _
      | add z1 z2 _ _ h1 h2 =>
        intro i
        have e2 : (fun k => qPi q P ((z1 + z2) k)) = (fun k => qPi q P (z1 k)) + (fun k => qPi q P (z2 k)) := by
          funext k; simp
        rw [e2, Matrix.mulVec_add]
        exact add_mem (h1 i) (h2 i)
      | smul a z1 _ h1 =>
        intro i
        have e2 : (fun k => qPi q P ((a • z1) k)) = qPi q P (a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => qPi q P (z1 k)) := by
          funext k
          show qPi q P ((a : E ⊗[F] Formalism.L2.Herm.Af F) * z1 k) = _
          rw [map_mul]; rfl
        rw [e2, Matrix.mulVec_smul]
        exact mul_mem (qdf_pi_int q P a.2) (h1 i)
    intro i j
    have hz : (fun k => (xm : Matrix (Fin n) (Fin n) _) k j) ∈ Formalism.L2.Herm.hatL (F := F)
        (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n)) := by
      refine (Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n)
        (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top xm _).2 ?_
      have e3 : (((xm⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          fun k => (xm : Matrix (Fin n) (Fin n) _) k j) = fun k => iA F E ((Pi.single j (1 : E) : Sp E n) k) := by
        have : (fun k => (xm : Matrix (Fin n) (Fin n) _) k j) =
            (xm : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ Pi.single j (1 : E ⊗[F] Formalism.L2.Herm.Af F) := by
          funext k; rw [Matrix.mulVec_single_one]; rfl
        rw [this, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        funext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      rw [e3]
      exact Submodule.subset_span ⟨Pi.single j 1, by
        have := single_mem_stdLat (E := E) (n := n) j 1
        simpa using this, rfl⟩
    have := key _ hz i
    have e7 : ((((bc (q.phi P) (qGL n fr))⁻¹ * q.at P xm : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) =
        ((((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          fun k => qPi q P ((xm : Matrix (Fin n) (Fin n) _) k j)) i := by
      rw [Units.val_mul, qdf_at_val]; rfl
    rw [e7]
    exact this
  ·
    intro i j
    have e0 : (((bc (q.phi P) (qGL n fr))⁻¹ * q.at P x)⁻¹ : GL (Fin n) _) = (q.at P x)⁻¹ * bc (q.phi P) (qGL n fr) := by
      rw [_root_.mul_inv_rev, inv_inv]
    rw [e0]
    have hcol : fr (Pi.single j 1) ∈ p.deco.1.at P.1 :=
      (p.2 P (Pi.single j 1)).2 ((mem_localization_standardLattice P.1 _).2 fun k => ⟨if k = j then 1 else 0, 1, P.1.isPrime.one_notMem, by
        by_cases hk : k = j <;> simp [Pi.single_apply, hk]⟩)
    obtain ⟨s, hs, hsN⟩ := (mem_locP P.1 _ _).1 hcol
    rw [hN] at hsN
    have hpull := (mem_globLat x.1 (s • fr (Pi.single j 1))).1 hsN
    obtain ⟨hne, hinv⟩ := qdf_phi_unit q P hs
    have e4 : ((((q.at P x)⁻¹ * bc (q.phi P) (qGL n fr) : GL (Fin n) _)) : Matrix (Fin n) (Fin n) _) i j =
        (q.phi P (s : E))⁻¹ * qPi q P (pullV x.1 (s • fr (Pi.single j 1)) i) := by
      have e5 : qPi q P (pullV x.1 (s • fr (Pi.single j 1)) i) =
          ((((q.at P x)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ fun k => q.phi P ((s • fr (Pi.single j 1)) k)) i := by
        unfold pullV
        rw [RingHom.map_mulVec, ← qdf_at_inv, qdf_at_val]
        rfl
      rw [e5]
      have e6 : (fun k => q.phi P ((s • fr (Pi.single j 1)) k)) = q.phi P (s : E) • fun k => q.phi P ((fr (Pi.single j 1)) k) := by
        funext k
        simp [Submodule.smul_def, Algebra.smul_def]
      rw [e6, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, Units.val_mul,
        Matrix.mul_apply]
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
    rw [e4]
    exact mul_mem hinv (qdf_pi_int q P (hpull i))

variable {H : Subgroup (GLG E n SG)}

def recClsFOf' (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ)
    (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q)
    (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c) : RecClsF hc n ST SG Q H q s :=
  recClsFOf hS hQ q (qdf_frLat q) qdf_frExists s hs

end QLat

end Formalism.L2.Col
