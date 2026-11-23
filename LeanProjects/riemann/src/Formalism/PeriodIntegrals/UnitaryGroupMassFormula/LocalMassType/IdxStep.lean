import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxGrp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.IsTopRingTens

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

def IdxHyp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P : Frame E n r) (Λ : Set (Fin n → E))
    (T : F) (μS0 : Measure (S0 (Fv F v) σ J P)) : Prop :=
  StdHyp σ J ψ ∧ P.IsStd σ J T ∧ IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧
    g.Prime ∧ (g : 𝓞 F) ∈ v.asIdeal ∧ Ideal.absNorm v.asIdeal = g ∧ etaV (E := E) v = 1 ∧
    IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) ∧ LocMassOrdW.IsLatLoc v Λ ∧ μS0.IsHaarMeasure ∧
    (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0

def UOgS {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (g r : ℕ) : AddSubgroup (UIdx r → Fv F v ⊗[F] E) where
  carrier := UOg (E := E) v g r
  zero_mem' := fun p => by rw [Pi.zero_apply, mul_zero]; exact oev_zero v
  add_mem' := fun ha hb p => by rw [Pi.add_apply, mul_add]; exact oev_add v (ha p) (hb p)
  neg_mem' := fun ha p => by rw [Pi.neg_apply, mul_neg]; exact oev_neg v (ha p)

def CongruenceSubgroupLift : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P : Frame E n r) (Λ : Set (Fin n → E))
    (T : F) (μS0 : Measure (S0 (Fv F v) σ J P)),
    IdxHyp σ J ψ v g P Λ T μS0 → K1 σ J v Λ g P ⊆ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v

def KUnip1 : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P : Frame E n r) (Λ : Set (Fin n → E))
    (T : F) (μS0 : Measure (S0 (Fv F v) σ J P)),
    IdxHyp σ J ψ v g P Λ T μS0 → ∀ u ∈ UO (E := E) v r,
    ∃ s ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, ∀ b, lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) =
      ∑ a, uMat v u a b • ratV (F := F) (Fv F v) (F0 P a)

def CongruenceSubgroupMeasurable : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P : Frame E n r) (Λ : Set (Fin n → E))
    (T : F) (μS0 : Measure (S0 (Fv F v) σ J P)),
    IdxHyp σ J ψ v g P Λ T μS0 → MeasurableSet (K1 σ J v Λ g P)

def MeasUOg : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (r g : ℕ), g.Prime → MeasurableSet (UOg (E := E) v g r)

def CountUOg : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (r g : ℕ), g.Prime →
    Countable ((UIdx r → Fv F v ⊗[F] E) ⧸ UOgS (E := E) v g r)

section Prf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}
  {Λ : Set (Fin n → E)}

theorem nat_osmul1 (g : ℕ) (w : Fv F v ⊗[F] E) :
    (g : v.adicCompletionIntegers F) • w = sc (E := E) v (g : Fv F v) * w := by
  have := congrFun (nat_osmul (n := 1) v g (fun _ => w)) 0
  simpa only [Pi.smul_apply, smul_eq_mul] using this

theorem natCast_ne {g : ℕ} (hg : g.Prime) : (g : Fv F v) ≠ 0 := by
  rw [← map_natCast (algebraMap F (Fv F v))]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hg.ne_zero)

theorem uMat_split {r : ℕ} (u : UIdx r → Fv F v ⊗[F] E) (a b : Fin (r + 1)) :
    uMat v u a b = (if a = b then 1 else 0) + (if h : a < b then u ⟨(a, b), h⟩ else 0) := by
  by_cases h1 : a = b
  · subst h1; simp [uMat]
  · by_cases h2 : a < b <;> simp [uMat, h1, h2]

theorem sum_uMat {r : ℕ} (u : UIdx r → Fv F v ⊗[F] E) (X : Fin (r + 1) → Fin n → Fv F v ⊗[F] E)
    (b : Fin (r + 1)) :
    ∑ a, uMat v u a b • X a = X b + ∑ a, (if h : a < b then u ⟨(a, b), h⟩ else 0) • X a := by
  simp only [uMat_split, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_dite_lt {r : ℕ} (b : Fin (r + 1))
    (c : {a // a ∈ {a : Fin (r + 1) | a < b}} → Fv F v ⊗[F] E) (X : Fin (r + 1) → Fin n → Fv F v ⊗[F] E) :
    ∑ a, (if h : a < b then c ⟨a, h⟩ else 0) • X a = ∑ i, c i • X i := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun a => a ∈ {a : Fin (r + 1) | a < b})
    (fun a => (if h : a < b then c ⟨a, h⟩ else 0) • X a)
  rw [← hsplit]
  have h0 : ∀ i : {x // ¬ x ∈ {a : Fin (r + 1) | a < b}},
      (if h : (i : Fin (r + 1)) < b then c ⟨i, h⟩ else 0) • X i = 0 := fun i => by
    rw [dif_neg (show ¬ ((i : Fin (r + 1)) < b) from i.2), zero_smul]
  simp only [h0, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos (show (i : Fin (r + 1)) < b from i.2)]

theorem ssub_frU {r : ℕ} (P : Frame E n r) {s : HA (Fv F v) σ J}
    (hs : s ∈ Ssub (Fv F v) σ J P) : ∃ u : UIdx r → Fv F v ⊗[F] E, ∀ b,
      lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) =
        ∑ a, uMat v u a b • ratV (F := F) (Fv F v) (F0 P a) := by
  have hs' : UniC (Fv F v) σ J (F0 P) s := hs
  have hc : ∀ b : Fin (r + 1), ∃ c : {a // a ∈ {a : Fin (r + 1) | a < b}} → Fv F v ⊗[F] E,
      ∑ i, c i • ratV (F := F) (Fv F v) (F0 P i) =
        lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) - ratV (F := F) (Fv F v) (F0 P b) :=
    fun b => (Fintype.mem_span_image_iff_exists_fun _).1 (hs' b)
  choose c hc using hc
  refine ⟨fun p => c p.1.2 ⟨p.1.1, p.2⟩, fun b => ?_⟩
  rw [sum_uMat]
  have := sum_dite_lt b (c b) (fun a => ratV (F := F) (Fv F v) (F0 P a))
  rw [this, hc b]
  abel

theorem ssub_of {r : ℕ} (P : Frame E n r) {s : HA (Fv F v) σ J} {u : UIdx r → Fv F v ⊗[F] E}
    (hs : ∀ b, lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) =
      ∑ a, uMat v u a b • ratV (F := F) (Fv F v) (F0 P a)) : s ∈ Ssub (Fv F v) σ J P := by
  intro b
  show lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) - ratV (F := F) (Fv F v) (F0 P b) ∈ _
  rw [hs b, sum_uMat, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun a _ => ?_
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, h, rfl⟩)
  · rw [zero_smul]; exact Submodule.zero_mem _

theorem kgv_iff {g : ℕ} (κ : HA (Fv F v) σ J) :
    κ ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v ↔ κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ∧
      ∀ w ∈ latLoc (E := E) v Λ, ∃ z ∈ latLoc (E := E) v Λ,
        lin (Fv F v) σ J κ w - w = sc (E := E) v (g : Fv F v) • z := by
  unfold Formalism.L2.SG.TypedSets.Kgv
  simp only [Set.mem_setOf_eq, Matrix.sub_mulVec, Matrix.one_mulVec, nat_osmul]
  exact Iff.rfl

theorem kgv_one {g : ℕ} : (1 : HA (Fv F v) σ J) ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v :=
  (kgv_iff 1).2 ⟨kv_one, fun w _ => ⟨0, Submodule.zero_mem _, by rw [lin_one, sub_self, smul_zero]⟩⟩

theorem kgv_mul {g : ℕ} {κ κ' : HA (Fv F v) σ J} (h : κ ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v)
    (h' : κ' ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v) : κ * κ' ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v := by
  rw [kgv_iff] at *
  refine ⟨kv_mul h.1 h'.1, fun w hw => ?_⟩
  obtain ⟨z', hz', hz'e⟩ := h'.2 w hw
  obtain ⟨z, hz, hze⟩ := h.2 w hw
  refine ⟨lin (Fv F v) σ J κ z' + z, Submodule.add_mem _ (kv_lat h.1 hz') hz, ?_⟩
  have e : lin (Fv F v) σ J (κ * κ') w - w =
      lin (Fv F v) σ J κ (lin (Fv F v) σ J κ' w - w) + (lin (Fv F v) σ J κ w - w) := by
    rw [lin_mul, map_sub]; abel
  rw [e, hz'e, hze, map_smul, smul_add]

theorem kgv_conj {g : ℕ} {s κ : HA (Fv F v) σ J} (hs : s ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (h : κ ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v) : s⁻¹ * κ * s ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v := by
  rw [kgv_iff] at *
  refine ⟨kv_mul (kv_mul (kv_inv hs) h.1) hs, fun w hw => ?_⟩
  obtain ⟨z, hz, hze⟩ := h.2 _ (kv_lat hs hw)
  refine ⟨lin (Fv F v) σ J s⁻¹ z, kv_lat (kv_inv hs) hz, ?_⟩
  have e : lin (Fv F v) σ J (s⁻¹ * κ * s) w - w =
      lin (Fv F v) σ J s⁻¹ (lin (Fv F v) σ J κ (lin (Fv F v) σ J s w) - lin (Fv F v) σ J s w) := by
    rw [map_sub, lin_inv_lin, lin_mul, lin_mul]
  rw [e, hze, map_smul]

theorem knat_mul {r g : ℕ} {P : Frame E n r} {x y : HA (Fv F v) σ J}
    (hx : x ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v) (hy : y ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v) :
    x * y ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v := by
  obtain ⟨hxK, s, κ, hsS, hsK, hκ, rfl⟩ := hx
  obtain ⟨hyK, s', κ', hsS', hsK', hκ', rfl⟩ := hy
  exact ⟨kv_mul hxK hyK, s * s', s'⁻¹ * κ * s' * κ', Subgroup.mul_mem (Ssub (Fv F v) σ J P) hsS hsS',
    kv_mul hsK hsK', kgv_mul (kgv_conj hsK' hκ) hκ', by group⟩

theorem knat_cong {r g : ℕ} {P : Frame E n r} (hP : IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))))
    {x : HA (Fv F v) σ J} (hx : x ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v) :
    ∃ u ∈ UO (E := E) v r, Cong σ J v Λ g P x u := by
  obtain ⟨-, s, κ, hsS, hsK, hκ, rfl⟩ := hx
  obtain ⟨u, hu⟩ := ssub_frU P hsS
  have hsX : ∀ b, locF v (s • ratTup (Fv F v) (F0 P)) b = locF v (frU v P u) b := fun b => by
    show sc (E := E) v (alp v r b) • lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) =
      sc (E := E) v (alp v r b) • ∑ a, uMat v u a b • ratV (F := F) (Fv F v) (F0 P a)
    rw [hu b]
  refine ⟨u, ?_, ?_⟩
  · rintro ⟨⟨a, b⟩, hab⟩
    have hin : locF v (frU v P u) b ∈ latLoc (E := E) v Λ := by
      rw [← hsX, locF_act]; exact kv_lat hsK (hP.1 b)
    unfold frU at hin
    rw [locF_comb] at hin
    have := hP.2 _ hin a
    have hu' : uMat v u a b = u ⟨(a, b), hab⟩ := by simp [uMat, hab.ne, hab]
    rw [hu'] at this
    exact this
  · intro b
    obtain ⟨z, hz, hze⟩ := ((kgv_iff κ).1 hκ).2 _ (hP.1 b)
    refine ⟨lin (Fv F v) σ J s z, kv_lat hsK hz, ?_⟩
    rw [← hsX, locF_act, locF_act, lin_mul, ← map_sub, hze, map_smul]

theorem uo_add {r g : ℕ} (hg : (g : Fv F v) ≠ 0) {u b : UIdx r → Fv F v ⊗[F] E}
    (hu : u ∈ UO (E := E) v r) (hb : b ∈ UOgS (E := E) v g r) : u + b ∈ UO (E := E) v r := by
  intro p
  rw [Pi.add_apply, mul_add]
  refine oev_add v (hu p) ?_
  have e : sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2) = sc (E := E) v (g : Fv F v) *
      sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2 * (g : Fv F v)⁻¹) := by
    rw [sc_mul', mul_comm (g : Fv F v), mul_assoc, inv_mul_cancel₀ hg, mul_one]
  rw [e, mul_assoc, ← nat_osmul1]
  have hb' := hb p
  rw [mem_oev_iff] at hb' ⊢
  exact Submodule.smul_mem _ _ hb'

def principalCongruenceSubgroupAlt (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (g : ℕ) (P : Frame E n r) : Subgroup (HA (Fv F v) σ J) where
  carrier := K1 σ J v Λ g P
  one_mem' := ⟨kv_one, fun b => ⟨0, Submodule.zero_mem _, by rw [one_smul, sub_self, smul_zero]⟩⟩
  mul_mem' := by
    rintro a c ⟨ha, ha'⟩ ⟨hc, hc'⟩
    refine ⟨kv_mul ha hc, fun b => ?_⟩
    obtain ⟨z, hz, hze⟩ := ha' b
    obtain ⟨z', hz', hz'e⟩ := hc' b
    refine ⟨lin (Fv F v) σ J a z' + z, Submodule.add_mem _ (kv_lat ha hz') hz, ?_⟩
    rw [locF_act] at hze hz'e ⊢
    have e : lin (Fv F v) σ J (a * c) (locF v (ratTup (Fv F v) (F0 P)) b) - locF v (ratTup (Fv F v) (F0 P)) b =
        lin (Fv F v) σ J a (lin (Fv F v) σ J c (locF v (ratTup (Fv F v) (F0 P)) b) -
          locF v (ratTup (Fv F v) (F0 P)) b) +
        (lin (Fv F v) σ J a (locF v (ratTup (Fv F v) (F0 P)) b) - locF v (ratTup (Fv F v) (F0 P)) b) := by
      rw [lin_mul, map_sub]; abel
    rw [e, hz'e, hze, map_smul, smul_add]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨kv_inv ha, fun b => ?_⟩
    obtain ⟨z, hz, hze⟩ := ha' b
    refine ⟨-lin (Fv F v) σ J a⁻¹ z, Submodule.neg_mem _ (kv_lat (kv_inv ha) hz), ?_⟩
    rw [locF_act] at hze ⊢
    have e : lin (Fv F v) σ J a⁻¹ (locF v (ratTup (Fv F v) (F0 P)) b) - locF v (ratTup (Fv F v) (F0 P)) b =
        -lin (Fv F v) σ J a⁻¹ (lin (Fv F v) σ J a (locF v (ratTup (Fv F v) (F0 P)) b) -
          locF v (ratTup (Fv F v) (F0 P)) b) := by
      rw [map_sub, lin_inv_lin]; abel
    rw [e, hze, map_smul, smul_neg]

def phi (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (g : ℕ) (P : Frame E n r) (x : HA (Fv F v) σ J) :
    UIdx r → Fv F v ⊗[F] E :=
  if h : ∃ u ∈ UO (E := E) v r, Cong σ J v Λ g P x u then h.choose else 0

theorem phi_spec {r g : ℕ} {P : Frame E n r} {x : HA (Fv F v) σ J}
    (h : ∃ u ∈ UO (E := E) v r, Cong σ J v Λ g P x u) :
    phi σ J v Λ g P x ∈ UO (E := E) v r ∧ Cong σ J v Λ g P x (phi σ J v Λ g P x) := by
  unfold phi; rw [dif_pos h]; exact h.choose_spec

theorem sdE_inv (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (ι : Type) [Fintype ι] :
    (sdE (E := E) ψ v ι).IsAddLeftInvariant := by
  unfold sdE
  split_ifs with h
  · haveI := h.choose_spec.1; infer_instance
  · exact ⟨fun _ => Measure.map_zero _⟩

end Prf

theorem stepIdx_of (hL : CongruenceSubgroupLift) (hU : KUnip1) (hM : CongruenceSubgroupMeasurable) (hMU : MeasUOg) (hC : CountUOg) :
    StepIdx := by
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μG μS0 hStd hP hSD hUn hg hgv hN hEta hPr hμG hLat hμS0 hS0
  have hyp : IdxHyp σ J ψ v g P Λ T μS0 := ⟨hStd, hP, hSD, hUn, hg, hgv, hN, hEta, hPr, hLat, hμS0, hS0⟩
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne hg
  haveI := hC (E := E) v r g hg
  haveI := sdE_inv (E := E) ψ v (UIdx r)
  have hNK : ∀ x ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v, ∀ k ∈ principalCongruenceSubgroupAlt σ J v Λ g P,
      x * k ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v :=
    fun x hx k hk => knat_mul hx (hL σ J ψ v g P Λ T μS0 hyp hk)
  have hφ : ∀ x ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v, phi σ J v Λ g P x ∈ UO (E := E) v r :=
    fun x hx => (phi_spec (knat_cong hPr hx)).1
  have hco : ∀ x ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v, ∀ y ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v,
      x⁻¹ * y ∈ principalCongruenceSubgroupAlt σ J v Λ g P ↔ -phi σ J v Λ g P x + phi σ J v Λ g P y ∈ UOgS (E := E) v g r :=
    fun x hx y hy => cong_iff hSD hPr hg0 hx.1 hy.1 (phi_spec (knat_cong hPr hx)).2
      (phi_spec (knat_cong hPr hy)).2
  have hsur : ∀ u ∈ UO (E := E) v r, ∃ x ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v,
      -phi σ J v Λ g P x + u ∈ UOgS (E := E) v g r := by
    intro u hu
    obtain ⟨s, hsK, hs⟩ := hU σ J ψ v g P Λ T μS0 hyp u hu
    have hsN : s ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v :=
      ⟨hsK, s, 1, ssub_of P hs, hsK, kgv_one, (mul_one s).symm⟩
    have hcs : Cong σ J v Λ g P s u := fun b => ⟨0, Submodule.zero_mem _, by
      rw [smul_zero, sub_eq_zero]
      show sc (E := E) v (alp v r b) • lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) =
        sc (E := E) v (alp v r b) • ∑ a, uMat v u a b • ratV (F := F) (Fv F v) (F0 P a)
      rw [hs b]⟩
    refine ⟨s, hsN, (cong_iff hSD hPr hg0 hsK hsK (phi_spec (knat_cong hPr hsN)).2 hcs).1 ?_⟩
    rw [inv_mul_cancel]
    exact (principalCongruenceSubgroupAlt σ J v Λ g P).one_mem
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : MeasurableAdd (Fv F v ⊗[F] E) := inferInstance
  haveI : MeasurableAdd (UIdx r → Fv F v ⊗[F] E) := inferInstance
  have key := idx_abs μG (sdE (E := E) ψ v (UIdx r)) (principalCongruenceSubgroupAlt σ J v Λ g P)
    (hM σ J ψ v g P Λ T μS0 hyp) (UOgS (E := E) v g r) (hMU (E := E) v r g hg)
    (Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v) (UO (E := E) v r) (phi σ J v Λ g P)
    hNK (fun u hu b hb => uo_add hg0 hu hb) hφ hco hsur
  have := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
  exact this

end PI.LocMassTypW
