import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistChar

theorem exists_mul_of_coprime {S : Type} [CommRing S] {M p : ℕ} (h : p.Coprime M) {z u w : S}
    (hu : z = M * u) (hw : z = p * w) : ∃ t, z = ((M * p : ℕ) : S) * t := by
  obtain ⟨α, β, hab⟩ : IsCoprime (p : S) (M : S) := Nat.Coprime.cast h
  refine ⟨α * u + β * w, ?_⟩
  push_cast
  linear_combination (α * p) * hu + (β * M) * hw - z * hab

theorem exists_proj {O S : Type} [CommRing O] [CommRing S] (ι : O →+* S) (bar : O →+* O) (c : S →+* S)
    (hbar : ∀ a, bar (bar a) = a) (hcc : ∀ z, c (c z) = z) (hc : ∀ a, c (ι a) = ι (bar a))
    (M p : ℕ) (hMp : p.Coprime M) (I : Ideal O) (hI : I * I.map bar = Ideal.span {(p : O)})
    (hII : I ⊔ I.map bar = ⊤)
    (hlift : ∀ b b' k : S, b * b' = 1 + ((M * p : ℕ) : S) * k → ∃ y : Sˣ, ∃ w, (y : S) = b + ((M * p : ℕ) : S) * w)
    (hdense : ∀ z : S, ∃ a w, z = ι a + p * w)
    (hcon : ∀ (a : O) (w : S), ι a = p * w → ∃ a', a = p * a') :
    ∃ π : S →+* O ⧸ I, (∀ z a, z - ι a ∈ I.map ι → π z = Ideal.Quotient.mk I a) ∧
      (∀ u : (O ⧸ I)ˣ, ∃ x : Sˣ, (x : S) * c x = 1 ∧ (∃ w, (x : S) - 1 = M * w) ∧ π x = u) ∧
      ∀ x : S, x * c x = 1 → (∃ w, x - 1 = M * w) → π x = 1 → ∃ w, x - 1 = ((M * p : ℕ) : S) * w := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hII)
  have hpII : (p : O) ∈ I * I.map bar := by rw [hI]; exact Ideal.mem_span_singleton_self _
  have hpI : (p : O) ∈ I := (Ideal.mul_le_inf (I := I) (J := I.map bar) hpII).1
  have hpS : (p : S) ∈ I.map ι := by simpa using Ideal.mem_map_of_mem ι hpI
  have hbj : bar j ∈ I := by
    have : I.map bar ≤ I.comap bar := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa [Ideal.mem_comap, hbar] using ha
    exact this hj
  have hmul : ∀ y ∈ I.map ι, ∀ z ∈ (I.map bar).map ι, ∃ w, y * z = p * w := by
    intro y hy z hz
    have := Ideal.mul_mem_mul hy hz
    rw [← Ideal.map_mul, hI, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at this
    exact this
  have hcomap : (I.map ι).comap ι ≤ I := by
    intro a ha
    obtain ⟨w, hw⟩ := hmul _ ha _ (Ideal.mem_map_of_mem ι hj)
    rw [← map_mul] at hw
    obtain ⟨a', ha'⟩ := hcon _ _ hw
    have : a = a * i + p * a' := by linear_combination ha' - a * hij
    rw [this]
    exact I.add_mem (I.mul_mem_left _ hi) (I.mul_mem_right _ hpI)
  let q : O ⧸ I →+* S ⧸ I.map ι := Ideal.quotientMap (I.map ι) ι Ideal.le_comap_map
  have hq : Function.Bijective q := by
    refine ⟨Ideal.quotientMap_injective' hcomap, fun z => ?_⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, w, rfl⟩ := hdense z
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ hpS
  let e := RingEquiv.ofBijective q hq
  let π : S →+* O ⧸ I := (e.symm : S ⧸ I.map ι →+* O ⧸ I).comp (Ideal.Quotient.mk _)
  have hπ : ∀ z a, π z = Ideal.Quotient.mk I a ↔ z - ι a ∈ I.map ι := by
    intro z a
    rw [← Ideal.Quotient.eq]
    exact e.symm_apply_eq
  refine ⟨π, fun z a => (hπ z a).2, fun u => ?_, fun x hx hM h1 => ?_⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : O ⧸ I)
    obtain ⟨a', ha'⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (O ⧸ I)ˣ) : O ⧸ I)
    have haa : a * a' - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, ha, ha', map_one, Units.mul_inv]
    obtain ⟨α, β, hab⟩ : IsCoprime (p : O) (M : O) := Nat.Coprime.cast hMp
    have hb : ∀ t : O, 1 + (t - 1) * j * β * M - t ∈ I := by
      intro t
      have : 1 + (t - 1) * j * β * M - t = (1 - t) * i + (1 - t) * j * α * p := by
        linear_combination (t - 1) * hij + (t - 1) * j * hab
      rw [this]
      exact I.add_mem (I.mul_mem_left _ hi) (I.mul_mem_left _ hpI)
    obtain ⟨b, hbdef⟩ : ∃ b, b = 1 + (a - 1) * j * β * M := ⟨_, rfl⟩
    obtain ⟨b', hbdef'⟩ : ∃ b', b' = 1 + (a' - 1) * j * β * M := ⟨_, rfl⟩
    have hba : b - a ∈ I := by rw [hbdef]; exact hb a
    have hba' : b' - a' ∈ I := by rw [hbdef']; exact hb a'
    have h1 : b * b' - 1 ∈ I := by
      have : b * b' - 1 = (b - a) * b' + a * (b' - a') + (a * a' - 1) := by ring
      rw [this]
      exact I.add_mem (I.add_mem (I.mul_mem_right _ hba) (I.mul_mem_left _ hba')) haa
    have h2 : b * b' - 1 = j * (M * (β * ((a - 1) + (a' - 1) * b))) := by
      rw [hbdef', hbdef]; ring
    have h3 : b * b' - 1 ∈ Ideal.span {(p : O)} := by
      have : b * b' - 1 = i * (b * b' - 1) + (b * b' - 1) * j := by linear_combination (1 - b * b') * hij
      rw [this, ← hI]
      exact Ideal.add_mem _ (Ideal.mul_mem_mul hi (h2 ▸ Ideal.mul_mem_right _ _ hj)) (Ideal.mul_mem_mul h1 hj)
    obtain ⟨w₁, hw₁⟩ := Ideal.mem_span_singleton.1 h3
    obtain ⟨t, ht⟩ := exists_mul_of_coprime hMp (u := j * (β * ((a - 1) + (a' - 1) * b)))
      (h2.trans (by ring)) hw₁
    obtain ⟨y, w, hy⟩ := hlift (ι b) (ι b') (ι t) (by
      rw [← map_mul, ← map_natCast ι, ← map_mul, ← ht, map_sub, map_one]; ring)
    have hcy : c y = ι (bar b) + ((M * p : ℕ) : S) * c w := by
      rw [hy, map_add, map_mul, map_natCast, hc]
    have hN : ∀ s : S, ((M * p : ℕ) : S) * s ∈ I.map ι := fun s => by
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hpS)
    have hbb : bar b = 1 + bar (a - 1) * bar j * bar β * M := by
      rw [hbdef]; simp only [map_add, map_mul, map_one, map_natCast]
    have hπy : π y = u := by
      rw [← ha, hπ, hy]
      have := Ideal.add_mem _ (Ideal.mem_map_of_mem ι hba) (hN w)
      convert this using 1
      rw [map_sub]; ring
    have hπc : π (c y) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), hπ, hcy]
      have h4 : bar b - 1 ∈ I := by
        rw [hbb, add_sub_cancel_left]
        exact I.mul_mem_right _ (I.mul_mem_right _ (I.mul_mem_left _ hbj))
      have := Ideal.add_mem _ (Ideal.mem_map_of_mem ι h4) (hN (c w))
      convert this using 1
      rw [map_sub]; ring
    let y' : Sˣ := Units.map (c : S →* S) y
    have hy' : (y' : S) = c y := rfl
    have hy'' : c y * ((y'⁻¹ : Sˣ) : S) = 1 := y'.mul_inv
    refine ⟨y * y'⁻¹, ?_, ⟨(ι ((a - 1) * j * β) - ι (bar (a - 1) * bar j * bar β) + p * (w - c w)) * (y'⁻¹ : Sˣ), ?_⟩, ?_⟩
    · have := congrArg c hy''
      rw [map_mul, hcc, map_one] at this
      rw [Units.val_mul, map_mul]
      linear_combination ((y : S) * c ((y'⁻¹ : Sˣ) : S)) * hy'' + this
    · have e1 : ι b = 1 + ι ((a - 1) * j * β) * M := by
        rw [hbdef, map_add, map_one, map_mul, map_natCast]
      have e2 : ι (bar b) = 1 + ι (bar (a - 1) * bar j * bar β) * M := by
        rw [hbb, map_add, map_one, map_mul, map_natCast]
      rw [Units.val_mul]
      push_cast at hy hcy
      linear_combination hy'' + ((y'⁻¹ : Sˣ) : S) * (hy - hcy + e1 - e2)
    · have := congrArg π hy''
      rw [map_mul, hπc, one_mul, map_one] at this
      rw [Units.val_mul, map_mul, this, mul_one, hπy]
  · obtain ⟨w, hw⟩ := hM
    rw [← map_one (Ideal.Quotient.mk I), hπ, map_one] at h1
    have h2 : c x - 1 ∈ (I.map bar).map ι := by
      have : I.map ι ≤ ((I.map bar).map ι).comap c := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, Ideal.mem_comap, hc]
        exact Ideal.mem_map_of_mem ι (Ideal.mem_map_of_mem bar ha)
      have := this h1
      rwa [Ideal.mem_comap, map_sub, map_one] at this
    obtain ⟨w₁, hw₁⟩ := hmul _ (Ideal.mem_map_of_mem ι hi) _ h2
    obtain ⟨w₂, hw₂⟩ := hmul _ h1 _ (Ideal.mem_map_of_mem ι hj)
    have hij' : ι i + ι j = 1 := by rw [← map_add, hij, map_one]
    refine exists_mul_of_coprime hMp hw (w := w₂ - x * w₁) ?_
    linear_combination hw₂ - x * hw₁ - (x - 1) * hij' + ι i * hx

open GlobalTheory.AdLat GlobalTheory.AdLat.RootNear

section Adelic

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_unit_lift (N : ℕ) (b b' k : intHat F E) (h : b * b' = 1 + (N : intHat F E) * k) :
    ∃ y : (intHat F E)ˣ, ∃ w, (y : intHat F E) = b + (N : intHat F E) * w := by
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) N
  have hu := unit_of_integral (inclHat F E) (inclHat_integral F E) (e * N) hun k
  have h1 := congrArg (inclHat F E) hee
  have h2 := congrArg (inclHat F E) hef
  rw [map_mul, map_natCast] at hu
  rw [map_mul] at h1
  rw [map_sub, map_one, map_mul, map_natCast] at h2
  generalize inclHat F E e = e' at *
  generalize inclHat F E f = f' at *
  have h3 : (e' * b + (1 - e')) * (e' * b' + (1 - e')) = 1 + e' * N * k := by
    linear_combination e' * h + (b * b' - b - b' + 1) * h1
  rw [← h3] at hu
  obtain ⟨y, hy⟩ := isUnit_of_mul_isUnit_left hu
  exact ⟨y, f' * (1 - b), by rw [hy]; linear_combination (1 - b) * h2⟩

theorem exists_ratHat_add (N : ℕ) (hN : 0 < N) (z : intHat F E) :
    ∃ a w, z = ratHat F E a + (N : intHat F E) * w := by
  obtain ⟨a, w, hw, h⟩ := GlobalTheory.CharFin.exists_int_add_nsmul F E N hN z z.2
  refine ⟨a, ⟨w, hw⟩, Subtype.ext ?_⟩
  rw [h, nsmul_eq_mul]
  push_cast
  rfl

theorem dvd_of_ratHat (N : ℕ) (hN : 0 < N) (a : 𝓞 E) (w : intHat F E) (h : ratHat F E a = (N : intHat F E) * w) :
    ∃ a', a = (N : 𝓞 E) * a' := by
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  let r : E →ₐ[F] RA F E := Algebra.TensorProduct.includeRight
  have h1 : r a = (N : RA F E) * w := by
    have := congrArg Subtype.val h
    push_cast at this
    exact this
  have h2 : r ((N : E)⁻¹ * a) = w := by
    rw [map_mul, h1, ← mul_assoc, ← map_natCast r, ← map_mul, inv_mul_cancel₀ hN', map_one, one_mul]
  obtain ⟨a', ha'⟩ := GlobalTheory.AdIdem.mem_range_of_one_tmul_mem F E (x := (N : E)⁻¹ * a) (by
    change r _ ∈ _
    rw [h2]; exact w.2)
  refine ⟨a', IsFractionRing.injective (𝓞 E) E ?_⟩
  rw [map_mul, ha', map_natCast, ← mul_assoc, mul_inv_cancel₀ hN', one_mul]

omit [NumberField E] in
theorem exists_mem_map_ideal_of_adelicCompletion (I : Ideal (𝓞 E)) (z : RA F E)
    (hz : z ∈ hat1 F ((algebraMap (𝓞 E) E) '' (I : Set (𝓞 E)))) :
    ∃ s ∈ I.map (ratHat F E), (s : RA F E) = z := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, _, ⟨s, hs, rfl⟩, rfl⟩ := hx
    refine ⟨⟨_, tmul_mem F E a ha 1⟩ * ratHat F E s, Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hs), ?_⟩
    change (a ⊗ₜ[F] (algebraMap (𝓞 E) E 1)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E s)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_one, one_mul]
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨s, hs, rfl⟩ := h1
    obtain ⟨t, ht, rfl⟩ := h2
    exact ⟨s + t, add_mem hs ht, rfl⟩
  | neg x _ h =>
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨-s, neg_mem hs, rfl⟩

omit [NumberField E] in
theorem sg_mem_intHat (c : E ≃ₐ[F] E) (z : RA F E) (hz : z ∈ intHat F E) :
    sg (FiniteAdeleRing (𝓞 F) F) c z ∈ intHat F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
    exact tmul_mem F E a ha (RingOfIntegers.mapRingEquiv (c : E ≃+* E) s)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg]; exact neg_mem h

omit [NumberField E] in
theorem sg_sg (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (z : RA F E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (sg (FiniteAdeleRing (𝓞 F) F) c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sg, hc]
  | add x y h1 h2 => simp only [map_add, h1, h2]

theorem exists_char (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (bar : 𝓞 E →+* 𝓞 E)
    (hbar : ∀ a, ((bar a : 𝓞 E) : E) = c a) (M p : ℕ) (hp : 0 < p) (hMp : p.Coprime M) (I : Ideal (𝓞 E))
    (hI : I * I.map bar = Ideal.span {(p : 𝓞 E)}) (hII : I ⊔ I.map bar = ⊤)
    (L : IntermediateField ℚ ℂ) (xi : (RA F E)ˣ →* ℂˣ)
    (tame : ∀ x : (RA F E)ˣ, (x : RA F E) * sg _ c x = 1 →
      (∃ w ∈ intHat F E, (x : RA F E) - 1 = (M * p) • w) → xi x = 1)
    (ram : ∃ x : (RA F E)ˣ, (x : RA F E) * sg _ c x = 1 ∧ (∃ w ∈ intHat F E, (x : RA F E) - 1 = M • w) ∧ xi x ≠ 1)
    (val : ∀ x : (RA F E)ˣ, (x : RA F E) * sg _ c x = 1 → ((xi x : ℂˣ) : ℂ) ∈ L) :
    ∃ χ : (𝓞 E ⧸ I)ˣ →* Lˣ, χ ≠ 1 ∧ ∀ (x : (RA F E)ˣ) (a : 𝓞 E) (u : (𝓞 E ⧸ I)ˣ),
      (x : RA F E) * sg _ c x = 1 → (∃ w ∈ intHat F E, (x : RA F E) - 1 = M • w) →
      (u : 𝓞 E ⧸ I) = Ideal.Quotient.mk I a →
      (x : RA F E) - 1 ⊗ₜ (a : E) ∈ hat1 F ((algebraMap (𝓞 E) E) '' (I : Set (𝓞 E))) →
      ((xi x : ℂˣ) : ℂ) = (((χ u : Lˣ) : L) : ℂ) := by
  let cS : intHat F E →+* intHat F E :=
    (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom.restrict _ _ (sg_mem_intHat F E c)
  have hcS : ∀ z : intHat F E, (cS z : RA F E) = sg _ c z := fun _ => rfl
  obtain ⟨π, hπ, hsur, hker⟩ := exists_proj (ratHat F E) bar cS
    (fun a => IsFractionRing.injective (𝓞 E) E (by
      change ((bar (bar a) : 𝓞 E) : E) = a
      rw [hbar, hbar, hc]))
    (fun z => Subtype.ext (sg_sg F E c hc z))
    (fun a => Subtype.ext (by
      change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c a) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((bar a : 𝓞 E) : E)
      rw [hbar]))
    M p hMp I hI hII (exists_unit_lift F E _) (exists_ratHat_add F E p hp) (dvd_of_ratHat F E p hp)
  let G : Subgroup (intHat F E)ˣ :=
    { carrier := {x | (x : intHat F E) * cS x = 1 ∧ ∃ w, (x : intHat F E) - 1 = M * w}
      one_mem' := ⟨by simp, 0, by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, w, hw⟩ ⟨hy, w', hw'⟩
        refine ⟨?_, w * y + w', ?_⟩
        · rw [Units.val_mul, map_mul]
          linear_combination ((y : intHat F E) * cS y) * hx + hy
        · rw [Units.val_mul]
          linear_combination (y : intHat F E) * hw + hw'
      inv_mem' := by
        rintro x ⟨hx, w, hw⟩
        refine ⟨?_, -(w * (x⁻¹ : (intHat F E)ˣ)), ?_⟩
        · have h1 := x.mul_inv
          have h2 := congrArg cS h1
          rw [map_mul, map_one] at h2
          linear_combination (-((x⁻¹ : (intHat F E)ˣ) : intHat F E) * cS (x⁻¹ : (intHat F E)ˣ)) * hx +
            (cS x * cS (x⁻¹ : (intHat F E)ˣ)) * h1 + h2
        · linear_combination x.mul_inv - ((x⁻¹ : (intHat F E)ˣ) : intHat F E) * hw }
  let incG : G →* (RA F E)ˣ := (Units.map ((intHat F E).subtype : intHat F E →* RA F E)).comp G.subtype
  have hinc : ∀ x : G, (incG x : RA F E) = ((x : (intHat F E)ˣ) : intHat F E) := fun _ => rfl
  have hnorm : ∀ x : G, (incG x : RA F E) * sg _ c (incG x) = 1 := fun x => congrArg Subtype.val x.2.1
  let φ : G →* (𝓞 E ⧸ I)ˣ := (Units.map (π : intHat F E →* 𝓞 E ⧸ I)).comp G.subtype
  have hφ : Function.Surjective φ := fun u => by
    obtain ⟨x, h1, h2, h3⟩ := hsur u
    exact ⟨⟨x, h1, h2⟩, Units.ext h3⟩
  let ξ₀ : G →* L :=
    { toFun := fun x => ⟨_, val _ (hnorm x)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  let ξ : G →* Lˣ := ξ₀.toHomUnits
  have hξ : ∀ x, (((ξ x : Lˣ) : L) : ℂ) = (xi (incG x) : ℂˣ) := fun _ => rfl
  have hle : φ.ker ≤ ξ.ker := by
    intro x hx
    obtain ⟨w, hw⟩ := hker _ x.2.1 x.2.2 (congrArg Units.val hx)
    have := tame _ (hnorm x) ⟨w, w.2, by
      have := congrArg Subtype.val hw
      rw [nsmul_eq_mul, hinc]
      push_cast at this ⊢
      exact this⟩
    refine Units.ext (Subtype.ext ?_)
    rw [hξ, this]
    rfl
  have hmk : ∀ x : (RA F E)ˣ, (x : RA F E) * sg _ c x = 1 → (∃ w ∈ intHat F E, (x : RA F E) - 1 = M • w) →
      ∃ g : G, incG g = x := by
    rintro x hx ⟨w, hw, h⟩
    have hxS : (x : RA F E) ∈ intHat F E := by
      rw [← sub_add_cancel (x : RA F E) 1, h]
      exact add_mem (nsmul_mem hw _) (one_mem _)
    have h1 : (⟨x, hxS⟩ : intHat F E) * cS ⟨x, hxS⟩ = 1 := Subtype.ext hx
    refine ⟨⟨⟨⟨x, hxS⟩, cS ⟨x, hxS⟩, h1, by rw [mul_comm]; exact h1⟩, h1, ⟨w, hw⟩, Subtype.ext ?_⟩, Units.ext rfl⟩
    rw [nsmul_eq_mul] at h
    push_cast
    exact h
  let χ : (𝓞 E ⧸ I)ˣ →* Lˣ := φ.liftOfSurjective hφ ⟨ξ, hle⟩
  have hχ : ∀ g, χ (φ g) = ξ g := fun g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  refine ⟨χ, fun h => ?_, fun x a u hx hM hu ha => ?_⟩
  · obtain ⟨x, h1, h2, h3⟩ := ram
    obtain ⟨g, rfl⟩ := hmk x h1 h2
    apply h3
    apply Units.ext
    rw [← hξ, ← hχ, h]
    rfl
  · obtain ⟨g, rfl⟩ := hmk x hx hM
    obtain ⟨s, hs, hs'⟩ := exists_mem_map_ideal_of_adelicCompletion F E I _ ha
    have : φ g = u := by
      apply Units.ext
      rw [hu]
      refine hπ _ a ?_
      convert hs using 1
      exact Subtype.ext hs'.symm
    rw [← this, hχ, hξ]

end Adelic

theorem exists_char_of_xiOK : ∀ (D : D7) (p : ℕ) (I : Ideal (𝓞 D.host.E)) (xi : (AfE D)ˣ →* ℂˣ), p.Prime → p.Coprime (D.host.g 0 * D.host.g 1) → I * I.map (barE D : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {((p : ℕ) : 𝓞 D.host.E)} → I ⊔ I.map (barE D : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ → XiOK D p xi → ∃ χ : (𝓞 D.host.E ⧸ I)ˣ →* (FO D)ˣ, χ ≠ 1 ∧ ∀ (x : (AfE D)ˣ) (a : 𝓞 D.host.E) (u : (𝓞 D.host.E ⧸ I)ˣ), NormOne x → CongOne (D.host.g 0 * D.host.g 1) x → (u : 𝓞 D.host.E ⧸ I) = Ideal.Quotient.mk I a → (x : AfE D) - 1 ⊗ₜ (a : D.host.E) ∈ GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (I : Set (𝓞 D.host.E))) → ((xi x : ℂˣ) : ℂ) = (((χ u : (FO D)ˣ) : FO D) : ℂ) := by
  intro D p I xi hp hcop hI hII h
  have hS : ∀ w, w ∈ intAE D ↔ w ∈ intHat D.host.F D.host.E := fun w => by
    rw [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]; rfl
  have hC : ∀ (N : ℕ) (x : (AfE D)ˣ), CongOne N x ↔
      ∃ w ∈ intHat D.host.F D.host.E, (x : AfE D) - 1 = N • w := fun N x => by
    simp only [CongOne, hS]
  obtain ⟨χ, h1, h2⟩ := exists_char D.host.F D.host.E (GlobalTheory.Member.cF D) (fun x => star_star x)
    (barE D : 𝓞 D.host.E →+* 𝓞 D.host.E) (fun _ => rfl) _ p hp.pos hcop I hI hII (FO D) xi
    (fun x hx hM => h.tame x hx ((hC _ x).2 hM))
    (by
      obtain ⟨x, h1, h2, h3⟩ := h.ram
      exact ⟨x, h1, (hC _ x).1 h2, h3⟩)
    h.val
  exact ⟨χ, h1, fun x a u hx hM => h2 x a u hx ((hC _ x).1 hM)⟩

end GlobalTheory.TwistChar
