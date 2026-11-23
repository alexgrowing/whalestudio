import Mathlib
import Lemmata.GeneralBFactLeftLast.Pz

noncomputable section

namespace Formalism.L2.NCov

open Module Module.End

section Ops

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem add_pow_apply_eq_zero {P Q : End K V} (h : Commute P Q) {x : V} {k l : ℕ}
    (hP : (P ^ k) x = 0) (hQ : (Q ^ l) x = 0) : ((P + Q) ^ (k + l)) x = 0 := by
  rw [h.add_pow, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, Module.End.mul_apply]
  suffices h0 : (P ^ m) ((Q ^ (k + l - m)) x) = 0 by rw [h0, smul_zero]
  rcases le_or_gt k m with hkm | hkm
  · obtain ⟨d, rfl⟩ : ∃ d, m = d + k := ⟨m - k, by omega⟩
    rw [← Module.End.mul_apply, (h.pow_pow (d + k) (k + l - (d + k))).eq, Module.End.mul_apply,
      pow_add, Module.End.mul_apply, hP, map_zero, map_zero]
  · obtain ⟨d, hd⟩ : ∃ d, k + l - m = d + l := ⟨k + l - m - l, by omega⟩
    rw [hd, pow_add, Module.End.mul_apply, hQ, map_zero, map_zero]

theorem commute_sub_smul {A B : End K V} (h : Commute A B) (a b : K) :
    Commute (A - a • 1) (B - b • 1) :=
  Commute.sub_left (Commute.sub_right h ((Commute.one_right A).smul_right b))
    ((Commute.one_left _).smul_left a)

theorem mem_maxGen_add {A B : End K V} (h : Commute A B) {a b : K} {x : V}
    (hA : x ∈ A.maxGenEigenspace a) (hB : x ∈ B.maxGenEigenspace b) :
    x ∈ (A + B).maxGenEigenspace (a + b) := by
  rw [mem_maxGenEigenspace] at hA hB ⊢
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  refine ⟨k + l, ?_⟩
  have e : A + B - (a + b) • (1 : End K V) = (A - a • 1) + (B - b • 1) := by
    rw [add_smul]; abel
  rw [e]
  exact add_pow_apply_eq_zero (commute_sub_smul h a b) hk hl

theorem mem_maxGen_mul {A B : End K V} (h : Commute A B) {a b : K} {x : V}
    (hA : x ∈ A.maxGenEigenspace a) (hB : x ∈ B.maxGenEigenspace b) :
    x ∈ (A * B).maxGenEigenspace (a * b) := by
  first | exact Bl.general_b_fact_left_last.goal1 .. | (apply Bl.general_b_fact_left_last.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_last.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_last.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_last.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_last.goal1 <;> first | assumption | infer_instance)

theorem maxGen_smul_one (c : K) : (c • (1 : End K V)).maxGenEigenspace c = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_maxGenEigenspace]
  exact ⟨1, by simp⟩

theorem eq_of_le_maxGen {W : Submodule K V} (hW : W ≠ ⊥) {f : End K V} {a b : K}
    (ha : W ≤ f.maxGenEigenspace a) (hb : W ≤ f.maxGenEigenspace b) : a = b := by
  by_contra hab
  exact hW (disjoint_self.1 ((f.disjoint_genEigenspace hab ⊤ ⊤).mono ha hb))

theorem finrank_finset_sup [FiniteDimensional K V] {ι : Type*} {p : ι → Submodule K V} (hp : iSupIndep p)
    (s : Finset ι) : finrank K ↥(s.sup p) = ∑ i ∈ s, finrank K ↥(p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hd : Disjoint (p a) (s.sup p) := by
      have := hp.disjoint_biSup (y := (s : Set ι)) (by simpa using ha)
      rw [Finset.sup_eq_iSup]
      simpa using this
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (p a) (s.sup p)
    rw [hd.eq_bot, finrank_bot, add_zero] at h2
    rw [Finset.sup_insert, Finset.sum_insert ha, h2, ih]

theorem iSup_eq_sup_filter {ι : Type*} (p : ι → Submodule K V) (F : Finset ι) (hF : ∀ i, p i ≠ ⊥ → i ∈ F)
    (P : ι → Prop) [DecidablePred P] : (⨆ (i) (_ : P i), p i) = (F.filter P).sup p := by
  apply le_antisymm
  · refine iSup₂_le fun i hi => ?_
    by_cases h : p i = ⊥
    · rw [h]; exact bot_le
    · exact Finset.le_sup (f := p) (Finset.mem_filter.2 ⟨hF i h, hi⟩)
  · exact Finset.sup_le fun i hi => le_iSup₂_of_le (f := fun i (_ : P i) => p i) i
      (Finset.mem_filter.1 hi).2 le_rfl

end Ops

section Alg

variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

def W (T : Subalgebra O (End K V)) (χ : T → K) : Submodule K V :=
  ⨅ t : T, (t : End K V).maxGenEigenspace (χ t)

def pt {T : Subalgebra O (End K V)} (ψ : T →ₐ[O] O) : T → K := fun t => algebraMap O K (ψ t)

theorem W_le (T : Subalgebra O (End K V)) (χ : T → K) (t : T) :
    W T χ ≤ (t : End K V).maxGenEigenspace (χ t) :=
  iInf_le (fun t : T => (t : End K V).maxGenEigenspace (χ t)) t

theorem algebraMap_end_eq (c : O) :
    algebraMap O (End K V) c = (algebraMap O K c) • (1 : End K V) := by
  ext x
  simp [Module.algebraMap_end_apply, algebraMap_smul]

theorem pt_injective {T : Subalgebra O (End K V)} (hinj : Function.Injective (algebraMap O K)) :
    Function.Injective (pt : (T →ₐ[O] O) → T → K) := fun ψ ψ' h =>
  AlgHom.ext fun t => hinj (congrFun h t)

variable [IsLocalRing O]

def cls {T : Subalgebra O (End K V)} (ψ : T →ₐ[O] O) : Ideal T :=
  RingHom.ker ((IsLocalRing.residue O).comp ψ.toRingHom)

def part (T : Subalgebra O (End K V)) (𝔪 : Ideal T) : Submodule K V :=
  ⨆ (ψ : T →ₐ[O] O) (_ : cls ψ = 𝔪), W T (pt ψ)

def off (T : Subalgebra O (End K V)) (𝔪 : Ideal T) : Submodule K V :=
  ⨆ (ψ : T →ₐ[O] O) (_ : cls ψ ≠ 𝔪), W T (pt ψ)

theorem cls_isMaximal {T : Subalgebra O (End K V)} (ψ : T →ₐ[O] O) : (cls ψ).IsMaximal := by
  refine RingHom.ker_isMaximal_of_surjective _ fun y => ?_
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨algebraMap O T c, by simp⟩

variable {S : Set (End K V)}

theorem commute_adjoin (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {a b : End K V}
    (ha : a ∈ Algebra.adjoin O S) (hb : b ∈ Algebra.adjoin O S) : Commute a b :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun b' hb' =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun a' ha' => hS b' hb' a' ha').symm

theorem chi_add (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {χ : Algebra.adjoin O S → K}
    (hW : W _ χ ≠ ⊥) (s t : Algebra.adjoin O S) : χ (s + t) = χ s + χ t :=
  eq_of_le_maxGen hW (W_le _ χ (s + t)) fun _ hx =>
    mem_maxGen_add (commute_adjoin hS s.2 t.2) (W_le _ χ s hx) (W_le _ χ t hx)

theorem chi_mul (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {χ : Algebra.adjoin O S → K}
    (hW : W _ χ ≠ ⊥) (s t : Algebra.adjoin O S) : χ (s * t) = χ s * χ t :=
  eq_of_le_maxGen hW (W_le _ χ (s * t)) fun _ hx =>
    mem_maxGen_mul (commute_adjoin hS s.2 t.2) (W_le _ χ s hx) (W_le _ χ t hx)

theorem chi_alg {χ : Algebra.adjoin O S → K} (hW : W _ χ ≠ ⊥) (c : O) :
    χ (algebraMap O (Algebra.adjoin O S) c) = algebraMap O K c := by
  refine eq_of_le_maxGen hW (W_le _ χ _) ?_
  rw [Subalgebra.coe_algebraMap, algebraMap_end_eq, maxGen_smul_one]
  exact le_top

theorem chi_int (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    {χ : Algebra.adjoin O S → K} (hW : W _ χ ≠ ⊥) (t : Algebra.adjoin O S) :
    χ t ∈ (algebraMap O K).range := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    exact hint x hx _ fun h => hW (eq_bot_iff.2 ((W_le _ χ ⟨x, Algebra.subset_adjoin hx⟩).trans h.le))
  | algebraMap r => exact ⟨r, (chi_alg hW r).symm⟩
  | add x y hx hy ihx ihy =>
    have e := chi_add hS hW ⟨x, hx⟩ ⟨y, hy⟩
    rw [show (⟨x + y, add_mem hx hy⟩ : Algebra.adjoin O S) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, e]
    exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    have e := chi_mul hS hW ⟨x, hx⟩ ⟨y, hy⟩
    rw [show (⟨x * y, mul_mem hx hy⟩ : Algebra.adjoin O S) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, e]
    exact mul_mem ihx ihy

theorem exists_pt (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (hinj : Function.Injective (algebraMap O K))
    {χ : Algebra.adjoin O S → K} (hW : W _ χ ≠ ⊥) :
    ∃ ψ : Algebra.adjoin O S →ₐ[O] O, pt ψ = χ := by
  have h := fun t => RingHom.mem_range.1 (chi_int hS hint hW t)
  choose f hf using h
  have h1 : f 1 = 1 := hinj (by rw [hf, map_one]; simpa using chi_alg hW (1 : O))
  have hm : ∀ s t, f (s * t) = f s * f t := fun s t => hinj (by rw [hf, map_mul, hf, hf, chi_mul hS hW])
  have h0 : f 0 = 0 := hinj (by rw [hf, map_zero]; simpa using chi_alg hW (0 : O))
  have ha : ∀ s t, f (s + t) = f s + f t := fun s t => hinj (by rw [hf, map_add, hf, hf, chi_add hS hW])
  have hc : ∀ c, f (algebraMap O (Algebra.adjoin O S) c) = c := fun c => hinj (by rw [hf, chi_alg hW])
  exact ⟨{ toFun := f, map_one' := h1, map_mul' := hm, map_zero' := h0, map_add' := ha, commutes' := hc },
    funext fun t => hf t⟩

theorem iSupIndep_alt (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) : iSupIndep (W (Algebra.adjoin O S)) :=
  independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun t : Algebra.adjoin O S => (t : End K V))
    fun i j φ => mapsTo_maxGenEigenspace_of_comm (commute_adjoin hS j.2 i.2) φ

theorem iSup_maxGen_eq_top [FiniteDimensional K V] (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) (t : Algebra.adjoin O S) :
    ⨆ μ, (t : End K V).maxGenEigenspace μ = ⊤ := by
  have hgen := iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun a : S => (a : End K V)) (fun a b _ => hS a a.2 b b.2) (fun a => hsplit a a.2)
  have key : ∀ χ : S → K, ∀ x (hx : x ∈ Algebra.adjoin O S), ∃ μ,
      (⨅ a : S, (a : End K V).maxGenEigenspace (χ a)) ≤ x.maxGenEigenspace μ := by
    intro χ x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact ⟨χ ⟨x, hx⟩, iInf_le (fun a : S => (a : End K V).maxGenEigenspace (χ a)) ⟨x, hx⟩⟩
    | algebraMap r =>
      exact ⟨algebraMap O K r, by rw [algebraMap_end_eq, maxGen_smul_one]; exact le_top⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, fun v hv => mem_maxGen_add (commute_adjoin hS hx hy) (ha hv) (hb hv)⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a * b, fun v hv => mem_maxGen_mul (commute_adjoin hS hx hy) (ha hv) (hb hv)⟩
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun χ => ?_
  obtain ⟨μ, hμ⟩ := key χ t t.2
  exact hμ.trans (le_iSup (fun μ => (t : End K V).maxGenEigenspace μ) μ)

theorem iSup_W_eq_top [FiniteDimensional K V] (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) : ⨆ χ, W (Algebra.adjoin O S) χ = ⊤ :=
  iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun t : Algebra.adjoin O S => (t : End K V)) (fun a b _ => commute_adjoin hS a.2 b.2)
    (iSup_maxGen_eq_top hS hsplit)

theorem exists_finset_pts [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) :
    ∃ F : Finset (Algebra.adjoin O S →ₐ[O] O),
      (∀ ψ, W _ (pt ψ) ≠ ⊥ → ψ ∈ F) ∧ F.sup (fun ψ => W _ (pt ψ)) = ⊤ := by
  have hind : iSupIndep (fun ψ : Algebra.adjoin O S →ₐ[O] O => W _ (pt ψ)) :=
    (iSupIndep_alt hS).comp (pt_injective hinj)
  have hfin := Submodule.finite_ne_bot_of_iSupIndep hind
  refine ⟨hfin.toFinset, fun ψ h => hfin.mem_toFinset.2 h, ?_⟩
  rw [eq_top_iff, ← iSup_W_eq_top (O := O) hS hsplit]
  refine iSup_le fun χ => ?_
  by_cases h : W _ χ = ⊥
  · rw [h]; exact bot_le
  · obtain ⟨ψ, rfl⟩ := exists_pt hS hint hinj h
    exact Finset.le_sup (f := fun ψ => W _ (pt ψ)) (hfin.mem_toFinset.2 h)

theorem sum_finrank_part [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (Ms : Finset (Ideal (Algebra.adjoin O S)))
    (hMs : ∀ 𝔪 : Ideal (Algebra.adjoin O S), 𝔪.IsMaximal → 𝔪 ∈ Ms) :
    ∑ 𝔪 ∈ Ms, finrank K (part (Algebra.adjoin O S) 𝔪) = finrank K V := by
  classical
  obtain ⟨F, hF, htop⟩ := exists_finset_pts hinj hS hsplit hint
  have hind : iSupIndep (fun ψ : Algebra.adjoin O S →ₐ[O] O => W _ (pt ψ)) :=
    (iSupIndep_alt hS).comp (pt_injective hinj)
  have hpart : ∀ 𝔪, part (Algebra.adjoin O S) 𝔪 =
      (F.filter (fun ψ => cls ψ = 𝔪)).sup (fun ψ => W _ (pt ψ)) := fun 𝔪 =>
    iSup_eq_sup_filter (fun ψ : Algebra.adjoin O S →ₐ[O] O => W _ (pt ψ)) F hF _
  calc ∑ 𝔪 ∈ Ms, finrank K (part (Algebra.adjoin O S) 𝔪)
      = ∑ 𝔪 ∈ Ms, ∑ ψ ∈ F with cls ψ = 𝔪, finrank K (W _ (pt ψ)) := by
        refine Finset.sum_congr rfl fun 𝔪 _ => ?_
        rw [hpart, finrank_finset_sup hind]
    _ = ∑ ψ ∈ F, finrank K (W _ (pt ψ)) :=
        Finset.sum_fiberwise_of_maps_to (fun ψ _ => hMs _ (cls_isMaximal ψ)) _
    _ = finrank K V := by rw [← finrank_finset_sup hind, htop, finrank_top]

theorem eq_zero_of_forall_mem_off [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (Ms : Finset (Ideal (Algebra.adjoin O S)))
    (hMs : ∀ 𝔪 : Ideal (Algebra.adjoin O S), 𝔪.IsMaximal → 𝔪 ∈ Ms)
    {y : V} (hy : ∀ 𝔪 ∈ Ms, y ∈ off (Algebra.adjoin O S) 𝔪) : y = 0 := by
  classical
  obtain ⟨F, hF, htop⟩ := exists_finset_pts hinj hS hsplit hint
  set Wp : (Algebra.adjoin O S →ₐ[O] O) → Submodule K V := fun ψ => W _ (pt ψ) with hWp
  have hind : iSupIndep Wp := (iSupIndep_alt hS).comp (pt_injective hinj)
  have hsi : F.SupIndep Wp := hind.supIndep' F
  have hoff : ∀ 𝔪, off (Algebra.adjoin O S) 𝔪 = (F.filter (fun ψ => cls ψ ≠ 𝔪)).sup Wp := fun 𝔪 =>
    iSup_eq_sup_filter Wp F hF _
  have key : ∀ s : Finset (Ideal (Algebra.adjoin O S)), (∀ 𝔪 ∈ s, y ∈ off (Algebra.adjoin O S) 𝔪) →
      y ∈ (F.filter (fun ψ => cls ψ ∉ s)).sup Wp := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have e : F.filter (fun ψ => cls ψ ∉ (∅ : Finset (Ideal (Algebra.adjoin O S)))) = F := by
        ext ψ; simp
      rw [e, htop]
      exact Submodule.mem_top
    | insert a s ha ih =>
      intro h
      have h1 := ih fun 𝔪 h𝔪 => h 𝔪 (Finset.mem_insert_of_mem h𝔪)
      have h2 := h a (Finset.mem_insert_self a s)
      rw [hoff] at h2
      have e1 : (F.filter (fun ψ => cls ψ ∉ s)).sup Wp =
          (F.filter (fun ψ => cls ψ ∉ insert a s)).sup Wp ⊔
            (F.filter (fun ψ => cls ψ ∉ s ∧ cls ψ = a)).sup Wp := by
        rw [← Finset.sup_union]
        congr 1
        ext ψ
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert]
        tauto
      have e2 : (F.filter (fun ψ => cls ψ ≠ a)).sup Wp =
          (F.filter (fun ψ => cls ψ ∉ insert a s)).sup Wp ⊔
            (F.filter (fun ψ => cls ψ ≠ a ∧ cls ψ ∈ s)).sup Wp := by
        rw [← Finset.sup_union]
        congr 1
        ext ψ
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert]
        tauto
      have hdis : Disjoint ((F.filter (fun ψ => cls ψ ∉ s ∧ cls ψ = a)).sup Wp)
          ((F.filter (fun ψ => cls ψ ≠ a)).sup Wp) :=
        hsi.disjoint_sup_sup (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          (Finset.disjoint_filter.2 fun ψ _ hx hx' => hx' hx.2)
      rw [e1] at h1
      rw [e2] at h2 hdis
      have hm := Submodule.mem_inf.2 ⟨h1, h2⟩
      rw [sup_inf_assoc_of_le _ le_sup_left, hdis.eq_bot, sup_bot_eq] at hm
      exact hm
  have hy' := key Ms hy
  have hempty : F.filter (fun ψ => cls ψ ∉ Ms) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun ψ _ hψ => hψ (hMs _ (cls_isMaximal ψ))
  rw [hempty, Finset.sup_empty] at hy'
  exact (Submodule.mem_bot K).1 hy'

end Alg

section Sat

open Polynomial

variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O]
  {S : Set (End K V)}

theorem pow_sub_apply_eq_zero [FiniteDimensional K V] (ψ : Algebra.adjoin O S →ₐ[O] O)
    (t : Algebra.adjoin O S) {x : V} (hx : x ∈ W _ (pt ψ)) :
    (((t : End K V) - algebraMap O (End K V) (ψ t)) ^
      ((t : End K V).maxGenEigenspaceIndex (pt ψ t))) x = 0 := by
  have h1 := W_le _ (pt ψ) t hx
  rw [maxGenEigenspace_eq, mem_genEigenspace_nat] at h1
  rw [algebraMap_end_eq]
  exact h1

set_option linter.deprecated false in

theorem exists_pt_of_isMaximal [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (𝔪 : Ideal (Algebra.adjoin O S)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ ψ : Algebra.adjoin O S →ₐ[O] O, W _ (pt ψ) ≠ ⊥ ∧ cls ψ = 𝔪 := by
  classical
  obtain ⟨F, hF, htop⟩ := exists_finset_pts hinj hS hsplit hint
  by_contra hne
  push Not at hne
  letI : CommRing (Algebra.adjoin O S) := Algebra.adjoinCommRingOfComm O fun a ha b hb => (hS a ha b hb).eq
  set F' := F.filter (fun ψ => W _ (pt ψ) ≠ ⊥) with hF'
  have ht : ∃ t ∈ 𝔪, ∀ ψ ∈ F', IsUnit (ψ t) := by
    rcases F'.eq_empty_or_nonempty with h0 | ⟨a, ha⟩
    · exact ⟨0, 𝔪.zero_mem, by simp [h0]⟩
    · have hcov : ¬ ((𝔪 : Set (Algebra.adjoin O S)) ⊆ ⋃ ψ ∈ (F' : Set (Algebra.adjoin O S →ₐ[O] O)),
          ((cls ψ : Ideal (Algebra.adjoin O S)) : Set (Algebra.adjoin O S))) := by
        intro hsub
        obtain ⟨ψ, hψ, hle⟩ :=
          (Ideal.subset_union_prime a a (fun ψ _ _ _ => (cls_isMaximal ψ).isPrime)).1 hsub
        exact hne ψ (Finset.mem_filter.1 hψ).2 (h𝔪.eq_of_le (cls_isMaximal ψ).ne_top hle).symm
      simp only [Set.not_subset, Set.mem_iUnion, not_exists] at hcov
      obtain ⟨t, htm, ht⟩ := hcov
      refine ⟨t, htm, fun ψ hψ => ?_⟩
      have h1 : t ∉ cls ψ := fun h => ht ψ hψ h
      change ¬ ((IsLocalRing.residue O) (ψ t) = 0) at h1
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1
  obtain ⟨t, htm, ht⟩ := ht
  let d : (Algebra.adjoin O S →ₐ[O] O) → ℕ := fun ψ => (t : End K V).maxGenEigenspaceIndex (pt ψ t)
  let P : O[X] := ∏ ψ ∈ F', (X - C (ψ t)) ^ d ψ
  have hP : aeval (t : End K V) P = 0 := by
    have hker : ∀ ψ ∈ F', W _ (pt ψ) ≤ LinearMap.ker (aeval (t : End K V) P) := by
      intro ψ hψ x hx
      rw [LinearMap.mem_ker]
      rw [show P = (∏ φ ∈ F'.erase ψ, (X - C (φ t)) ^ d φ) * (X - C (ψ t)) ^ d ψ from
        (Finset.prod_erase_mul _ _ hψ).symm]
      rw [map_mul, Module.End.mul_apply, map_pow, map_sub, aeval_X, aeval_C]
      rw [pow_sub_apply_eq_zero ψ t hx, map_zero]
    have htop' : F'.sup (fun ψ => W _ (pt ψ)) = ⊤ := by
      rw [← htop]
      apply le_antisymm
      · exact Finset.sup_mono (Finset.filter_subset _ _)
      · refine Finset.sup_le fun ψ hψ => ?_
        by_cases h : W _ (pt ψ) = ⊥
        · rw [h]; exact bot_le
        · exact Finset.le_sup (f := fun ψ => W _ (pt ψ)) (Finset.mem_filter.2 ⟨hψ, h⟩)
    have hle : (⊤ : Submodule K V) ≤ LinearMap.ker (aeval (t : End K V) P) := by
      rw [← htop']; exact Finset.sup_le hker
    ext x
    exact LinearMap.mem_ker.1 (hle Submodule.mem_top)
  have hPT : aeval t P = 0 := by
    apply Subtype.val_injective
    have e := aeval_algHom_apply (Algebra.adjoin O S).val t P
    simp only [Subalgebra.coe_val] at e
    rw [← e]
    simpa using hP
  have hu : IsUnit (P.coeff 0) := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun ψ hψ => ?_
    simp only [eval_pow, eval_sub, eval_X, eval_C, zero_sub]
    exact ((ht ψ hψ).neg).pow _
  obtain ⟨u, hu'⟩ := hu
  have key := congrArg (aeval t) (X_mul_divX_add P)
  rw [hPT, map_add, map_mul, aeval_X, aeval_C, ← hu'] at key
  have e : t * aeval t P.divX = - algebraMap O _ (u : O) := eq_neg_of_add_eq_zero_left key
  have hunitT : IsUnit t := by
    have h : t * (aeval t P.divX * algebraMap O _ (-↑u⁻¹)) = 1 := by
      rw [← mul_assoc, e, ← map_neg, ← map_mul, neg_mul_neg, Units.mul_inv, map_one]
    exact ⟨⟨t, _, h, (mul_comm _ t).trans h⟩, rfl⟩
  exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem 𝔪 htm hunitT)

theorem isCompl_part_off [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (𝔪 : Ideal (Algebra.adjoin O S)) :
    IsCompl (part (Algebra.adjoin O S) 𝔪) (off (Algebra.adjoin O S) 𝔪) := by
  classical
  obtain ⟨F, hF, htop⟩ := exists_finset_pts hinj hS hsplit hint
  set Wp : (Algebra.adjoin O S →ₐ[O] O) → Submodule K V := fun ψ => W _ (pt ψ) with hWp
  have hind : iSupIndep Wp := (iSupIndep_alt hS).comp (pt_injective hinj)
  have hsi : F.SupIndep Wp := hind.supIndep' F
  have hpart : part (Algebra.adjoin O S) 𝔪 = (F.filter (fun ψ => cls ψ = 𝔪)).sup Wp :=
    iSup_eq_sup_filter Wp F hF _
  have hoff : off (Algebra.adjoin O S) 𝔪 = (F.filter (fun ψ => cls ψ ≠ 𝔪)).sup Wp :=
    iSup_eq_sup_filter Wp F hF _
  rw [hpart, hoff]
  constructor
  · exact hsi.disjoint_sup_sup (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (Finset.disjoint_filter.2 fun ψ _ h h' => h' h)
  · rw [codisjoint_iff, ← Finset.sup_union]
    have e : F.filter (fun ψ => cls ψ = 𝔪) ∪ F.filter (fun ψ => cls ψ ≠ 𝔪) = F := by
      ext ψ; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    rw [e]; exact htop

end Sat

end Formalism.L2.NCov
