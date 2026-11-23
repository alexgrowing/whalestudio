import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehom
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

section Loc

variable {σ : Type}

def kerPt (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ) :=
  RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)

instance kerPt_isPrime (z : σ → ℂ) : (kerPt z).IsPrime :=
  RingHom.ker_isPrime _

def kerPtQ (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ ⧸ I) :=
  (kerPt z).map (Ideal.Quotient.mk I)

theorem mk_mem_kerPtQ {I : Ideal (MvPolynomial σ ℂ)} {z : σ → ℂ} (hI : I ≤ kerPt z)
    (f : MvPolynomial σ ℂ) : Ideal.Quotient.mk I f ∈ kerPtQ I z ↔ f ∈ kerPt z :=
  Ideal.mem_quotient_iff_mem hI

theorem kerPtQ_isPrime {I : Ideal (MvPolynomial σ ℂ)} {z : σ → ℂ} (hI : I ≤ kerPt z) :
    (kerPtQ I z).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI)

abbrev locQ (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Type :=
  Localization.AtPrime (kerPt z) ⧸
    Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (kerPt z))) I

theorem algebraMap_locQ_mk (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) (f : MvPolynomial σ ℂ) :
    algebraMap (MvPolynomial σ ℂ ⧸ I) (locQ I z) (Ideal.Quotient.mk I f) =
      algebraMap _ (locQ I z) f := by
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.mk_algebraMap]

theorem isLocalization_locQ {I : Ideal (MvPolynomial σ ℂ)} {z : σ → ℂ} (hI : I ≤ kerPt z) :
    letI := kerPtQ_isPrime hI; IsLocalization.AtPrime (locQ I z) (kerPtQ I z) := by
  let _ := kerPtQ_isPrime hI
  set P := kerPt z
  have hmem : ∀ f, Ideal.Quotient.mk I f ∈ (kerPtQ I z).primeCompl ↔ f ∈ P.primeCompl :=
    fun f => not_congr (mk_mem_kerPtQ hI f)
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [algebraMap_locQ_mk, ← Ideal.Quotient.mk_algebraMap]
    exact (IsLocalization.map_units (Localization.AtPrime P) (⟨f, (hmem f).1 hy⟩ : P.primeCompl)).map _
  · intro w
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl s
    refine ⟨(Ideal.Quotient.mk I a, ⟨Ideal.Quotient.mk I b, (hmem b).2 b.2⟩), ?_⟩
    simp only [algebraMap_locQ_mk, ← Ideal.Quotient.mk_algebraMap, ← map_mul]
    exact congrArg _ hab
  · intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [algebraMap_locQ_mk, algebraMap_locQ_mk, ← Ideal.Quotient.mk_algebraMap,
      ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, ← map_sub] at huv
    obtain ⟨⟨k, s⟩, hks⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (M := P.primeCompl) (S := Localization.AtPrime P)).1 huv
    rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hks
    obtain ⟨c, hc⟩ := hks
    refine ⟨⟨Ideal.Quotient.mk I s, (hmem s).2 s.2⟩, ?_⟩
    have hc0 : (c : MvPolynomial σ ℂ) ≠ 0 := fun h => c.2 (h ▸ P.zero_mem)
    have hk : (a - b) * s = k := mul_left_cancel₀ hc0 hc
    show Ideal.Quotient.mk I s * Ideal.Quotient.mk I a = Ideal.Quotient.mk I s * Ideal.Quotient.mk I b
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mul_comm, hk]
    exact k.2

end Loc

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_closedPoint_stalk' {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : projX P hP) (hx : x ∈ (chartOpen hP p).1)
    (hc : IsClosed ({x} : Set (projX P hP))) :
    ∃ y : (Σ k, ι k) → ℂ, (∀ h ∈ chartIdeal P p, eval y h = 0) ∧
      (∀ q, val (toSpecC hP) (chartCoord hP p q) x hx = y q) ∧
      Nonempty ((projX P hP).presheaf.stalk x ≃+* locQ (chartIdeal P p) y) := by
  have hU : IsAffineOpen (chartOpen hP p).1 := (chartOpen hP p).2
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP p).1 x hx hc
  let e := gammaChart hP p
  let y : (Σ k, ι k) → ℂ := fun q => val (toSpecC hP) (chartCoord hP p q) x hx
  have hψ : φ.comp (e.symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal P p))) = eval y := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, eval_C]
      rw [gammaChart_symm_C, hφ, val_const (toSpecC hP) _ x hx hc]
    · intro q
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, eval_X]
      rw [hφ]
      rfl
  have hev : ∀ f, φ (e.symm (Ideal.Quotient.mk _ f)) = eval y f := fun f => RingHom.congr_fun hψ f
  have hzero : ∀ h ∈ chartIdeal P p, eval y h = 0 := by
    intro h hh
    rw [← hev, Ideal.Quotient.eq_zero_iff_mem.2 hh, map_zero, map_zero]
  have hI : chartIdeal P p ≤ kerPt y := fun h hh => (RingHom.mem_ker).2 (hzero h hh)
  refine ⟨y, hzero, fun q => rfl, ?_⟩
  let _ := TopCat.Presheaf.algebra_section_stalk (projX P hP).presheaf (⟨x, hx⟩ : (chartOpen hP p).1)
  have := hU.isLocalization_stalk ⟨x, hx⟩
  set Q := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let _ := kerPtQ_isPrime hI
  have hloc := isLocalization_locQ hI
  have hQ : ∀ a, a ∈ Q ↔ φ a = 0 := by
    intro a
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((projX P hP).presheaf.stalk x) Q, hφ,
      val_eq_zero_iff (toSpecC hP) a x hx hc, ← Scheme.germ_residue, CommRingCat.comp_apply]
    exact (IsLocalRing.residue_eq_zero_iff _).symm
  have key : ∀ f, e.symm (Ideal.Quotient.mk _ f) ∈ Q ↔
      Ideal.Quotient.mk (chartIdeal P p) f ∈ kerPtQ (chartIdeal P p) y := by
    intro f
    rw [hQ, hev, mk_mem_kerPtQ hI]
    rfl
  have H : Q.primeCompl.map e.toMonoidHom = (kerPtQ (chartIdeal P p) y).primeCompl := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      show e a ∉ kerPtQ _ y
      obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e a)
      have ha' : a = e.symm (Ideal.Quotient.mk _ f) := by rw [hf, e.symm_apply_apply]
      rw [← hf, ← key f, ← ha']
      exact ha
    · intro hb
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨e.symm (Ideal.Quotient.mk _ f), ?_, e.apply_symm_apply _⟩
      show _ ∉ Q
      rw [key]
      exact hb
  exact ⟨IsLocalization.ringEquivOfRingEquiv ((projX P hP).presheaf.stalk x)
    (locQ (chartIdeal P p) y) e H⟩

end

end ReciprocityTheory.AnForm.R
