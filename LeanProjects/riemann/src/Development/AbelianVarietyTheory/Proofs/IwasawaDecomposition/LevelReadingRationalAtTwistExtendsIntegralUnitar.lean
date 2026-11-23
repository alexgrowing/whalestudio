import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruenceOneMatricesMemNhdsOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalAtPrimesUnitaryCongruentOneStatement

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev.Approx

theorem underPl_conjP {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (P : HeightOneSpectrum (𝓞 E)) : underPl F (conjPrime₂ P) = underPl F P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [underPl_asIdeal, underPl_asIdeal, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, rll_cO_algebraMap hc]

theorem conjP_notMem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ1 : ∀ P : Q, conjPrime₂ P.1 ≠ P.1)
    (hQ2 : ∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P') : ∀ P ∈ Q, conjPrime₂ P ∉ Q := by
  intro P hP hP'
  have h := hQ2 ⟨P, hP⟩ ⟨conjPrime₂ P, hP'⟩ (underPl_conjP hc P).symm
  exact hQ1 ⟨P, hP⟩ (congrArg Subtype.val h).symm

theorem red_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} [NeZero n] (a : 𝓞 E) (ha : a ≠ 0) {u : GL (Fin n) (AfE F E)} (hu : u ∈ UAd hc n)
    (h : GlobalTheory.Mem.ColAd.CongOne a u) :
    ∃ hS : u ∈ St (1 : GL (Fin n) (AfE F E)), ∀ w : HeightOneSpectrum (𝓞 E), a ∈ w.asIdeal →
      redAt (1 : GL (Fin n) (AfE F E)) w ⟨u, hS⟩ = 1 := by
  classical
  have hca : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) *
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (by simpa using ha), map_one]
  have hs : ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j = (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j +
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) * (⟨_, h i j⟩ : Formalism.L2.Herm.intAf F E) := by
    intro i j
    show _ = _ + _ * (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ * _)
    rw [← mul_assoc, hca, one_mul]
    ring
  obtain ⟨s, hs⟩ : ∃ s : Fin n → Fin n → Formalism.L2.Herm.intAf F E, ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j =
      (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j + Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) * s i j :=
    ⟨fun i j => ⟨_, h i j⟩, hs⟩
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hi : ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E := by
    intro i j
    rw [hs]
    exact add_mem (hone i j) (mul_mem (iA_mem a) (s i j).2)
  have hSt := rlt_mem_St hc n hu hi
  obtain ⟨y, hy, hred⟩ := St_one_int hSt
  refine ⟨hSt, fun P hP => ?_⟩
  apply Units.ext
  ext i j
  rw [hred P i j]
  have e : y i j = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j + oToS F E a * s i j := by
    apply Subtype.ext
    rw [← hy, hs]
    simp only [Subring.coe_add, Subring.coe_mul]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  rw [e, map_add, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hP, zero_mul, add_zero]
  show _ = (1 : Matrix (Fin n) (Fin n) (kP P)) i j
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.SeeSaw.TwLev.Approx

namespace GlobalTheory.SeeSaw.TwLev.Approx

theorem rd_all : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n : ℕ} [NeZero n] {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {J : Matrix (Fin n) (Fin n) E}, J = 1 →
    ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ),
    (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → (∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P') →
    (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F);
      ∀ᶠ (u : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) →
    RdLevOn hc (RatAt Q) S.U S.chi Λ emb Q HQ lamQ →
    RdLevOn hc Set.univ S.U S.chi Λ emb Q HQ lamQ := by
  intro F E K _ _ _ _ _ _ _ hc n _ SG Q J hJ T f bad S Λ emb HQ lamQ hQ1 hQ2 hO hR
  subst hJ
  classical
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  have hQc := conjP_notMem hc hQ1 hQ2
  have h1U : (1 : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) ∈
      {x : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ S.U} := S.U.one_mem
  obtain ⟨V, hV, hVsub⟩ := (mem_nhds_subtype _ _ _).1 (S.U_open.mem_nhds h1U)
  obtain ⟨m₀, hm₀, hm₀N⟩ := GlobalTheory.T.congruenceOne_matrices_mem_nhds_one (F := F) (E := E) n (V ∩ {u | ∀ κ : S.U, κ.1 = u → S.chi κ = 1})
    (Filter.inter_mem hV hO)
  set m : ℕ := m₀ * ∏ w ∈ SG ∪ Q, Ideal.absNorm w.asIdeal with hm
  have hmpos : 0 < m := Nat.mul_pos hm₀ (Finset.prod_pos fun w _ =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot))
  have hmw : ∀ w ∈ SG ∪ Q, ((m : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    intro w hw
    obtain ⟨k, hk⟩ : Ideal.absNorm w.asIdeal ∣ m := Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hw) _
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  intro z _ hz hzU
  obtain ⟨g, hgU, hgR, hc1, hc2⟩ := GlobalTheory.T.exists_rationalAtPrimes_unitary_congruentOne hc hQc m hmpos (fun P hP => hmw P (Finset.mem_union_right _ hP)) z hzU hz
  set u := z⁻¹ * g with hu
  have huU : u ∈ UAd hc n := mul_mem (inv_mem hzU) hgU
  have huN := hm₀N m (Dvd.intro _ rfl) hmpos u hc1 hc2
  have huS : u ∈ S.U := hVsub (a := ⟨u, huU⟩) huN.1
  have hchiu : S.chi ⟨u, huS⟩ = 1 := huN.2 ⟨u, huS⟩ rfl
  obtain ⟨huSt, hred⟩ := red_eq_one hc (m : 𝓞 E) (by exact_mod_cast hmpos.ne') huU hc1
  have hzg : g = z * u := by rw [hu, mul_inv_cancel_left]
  have hgSt : g ∈ St (1 : GL (Fin n) (AfE F E)) := hzg ▸ mul_mem hz huSt
  have hredg : ∀ w ∈ SG ∪ Q, redAt (1 : GL (Fin n) (AfE F E)) w ⟨g, hgSt⟩ = redAt 1 w ⟨z, hz⟩ := by
    intro w hw
    have e : (⟨g, hgSt⟩ : St (1 : GL (Fin n) (AfE F E))) = ⟨z, hz⟩ * ⟨u, huSt⟩ := Subtype.ext hzg
    rw [e, map_mul, hred w (hmw w hw), mul_one]
  obtain ⟨hiff, hchi⟩ := hR g hgR hgSt hgU
  have hgz : g ∈ S.U ↔ z ∈ S.U := by
    rw [hzg]
    exact ⟨fun h => by simpa using mul_mem h (inv_mem huS), fun h => mul_mem h huS⟩
  have hSGr : ∀ w : SG, redAt (1 : GL (Fin n) (AfE F E)) w.1 ⟨g, hgSt⟩ = redAt 1 w.1 ⟨z, hz⟩ :=
    fun w => hredg w.1 (Finset.mem_union_left _ w.2)
  have hQr : ∀ P : Q, redAt (1 : GL (Fin n) (AfE F E)) P.1 ⟨g, hgSt⟩ = redAt 1 P.1 ⟨z, hz⟩ :=
    fun P => hredg P.1 (Finset.mem_union_right _ P.2)
  refine ⟨?_, ?_⟩
  · rw [← hgz, hiff]
    simp only [hSGr, hQr]
  · intro hU h h'
    have hgU' : g ∈ S.U := hgz.2 hU
    have e1 := hchi hgU' (fun w => (hSGr w).symm ▸ h w) (fun P => (hQr P).symm ▸ h' P)
    have e2 : S.chi ⟨g, hgU'⟩ = S.chi ⟨z, hU⟩ := by
      have : (⟨g, hgU'⟩ : S.U) = ⟨z, hU⟩ * ⟨u, huS⟩ := Subtype.ext hzg
      rw [this, map_mul, hchiu, mul_one]
    rw [← e2, e1]
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [show (⟨_, (hSGr w).symm ▸ h w⟩ : (Λ w).H) = ⟨_, h w⟩ from Subtype.ext (hSGr w)]
    · refine Finset.prod_congr rfl fun P _ => ?_
      rw [show (⟨_, (hQr P).symm ▸ h' P⟩ : HQ P) = ⟨_, h' P⟩ from Subtype.ext (hQr P)]

end GlobalTheory.SeeSaw.TwLev.Approx
