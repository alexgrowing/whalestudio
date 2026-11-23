import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

private def eOne (X : Type) [CommRing X] [Algebra A X] (j : Fin g) (M : Matrix (Fin n) (Fin n) A) :
    Matrix (Fin n) (Fin n) (DD X g) := DD.epM (Pi.single j (M.map (algebraMap A X)))

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

end SlopeTestRemainingChoices

section Conj

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X]

end Conj

end UpperTheory.V.Pa

private theorem dd_ep_finset_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (m : Fin g) :
    (∑ c ∈ s, f c).ep m = ∑ c ∈ s, (f c).ep m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DD.add_ep, ih]

private theorem ep_component_add {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ c ∈ s, f c).a = ∑ c ∈ s, (f c).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_a]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DD.add_a, ih]

private theorem dd_ep'_finset_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (m : Fin g) :
    (∑ c ∈ s, f c).ep' m = ∑ c ∈ s, (f c).ep' m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DD.add_ep', ih]

private theorem dd_eta_finset_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ c ∈ s, f c).eta = ∑ c ∈ s, (f c).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_eta]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DD.add_eta, ih]

private theorem epM_mul_epM_eq_zero {X : Type} [CommRing X] {g n : ℕ} (f f' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM f * DD.epM f' = 0 := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [Matrix.mul_apply, ep_component_add, DD.mul_a, DD.epM, DD.zero_a]
  · funext m
    simp [Matrix.mul_apply, dd_ep_finset_sum, DD.mul_ep, DD.epM, DD.zero_ep]
  · funext m
    simp [Matrix.mul_apply, dd_ep'_finset_sum, DD.mul_ep', DD.epM, DD.zero_ep']
  · simp [Matrix.mul_apply, dd_eta_finset_sum, DD.mul_eta, DD.epM, DD.zero_eta]

private theorem map_C_mul_epM {X : Type} [CommRing X] {g n : ℕ} (P : Matrix (Fin n) (Fin n) X) (f : Fin g → Matrix (Fin n) (Fin n) X) :
    P.map DD.C * DD.epM f = DD.epM (fun m => P * f m) := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [Matrix.mul_apply, ep_component_add, DD.mul_a, DD.epM]
  · funext m
    simp [Matrix.mul_apply, dd_ep_finset_sum, DD.mul_ep, DD.epM, DD.C_ep, DD.C_a]
  · funext m
    simp [Matrix.mul_apply, dd_ep'_finset_sum, DD.mul_ep', DD.epM, DD.C_ep', DD.C_a]
  · simp [Matrix.mul_apply, dd_eta_finset_sum, DD.mul_eta, DD.epM, DD.C_eta, DD.C_ep, DD.C_ep']

private theorem epM_mul_map_C {X : Type} [CommRing X] {g n : ℕ} (P : Matrix (Fin n) (Fin n) X) (f : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM f * P.map DD.C = DD.epM (fun m => f m * P) := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [Matrix.mul_apply, ep_component_add, DD.mul_a, DD.epM]
  · funext m
    simp [Matrix.mul_apply, dd_ep_finset_sum, DD.mul_ep, DD.epM, DD.C_ep, DD.C_a]
  · funext m
    simp [Matrix.mul_apply, dd_ep'_finset_sum, DD.mul_ep', DD.epM, DD.C_ep', DD.C_a]
  · simp [Matrix.mul_apply, dd_eta_finset_sum, DD.mul_eta, DD.epM, DD.C_eta, DD.C_ep, DD.C_ep']

private theorem epM_pi_add {X : Type} [CommRing X] {g n : ℕ} (f f' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (f + f') = DD.epM f + DD.epM f' := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [DD.add_a, DD.epM]
  · funext m
    simp [DD.add_ep, DD.epM]
  · funext m
    simp [DD.add_ep', DD.epM]
  · simp [DD.add_eta, DD.epM]

private theorem epM_pi_zero {X : Type} [CommRing X] {g n : ℕ} :
    DD.epM (0 : Fin g → Matrix (Fin n) (Fin n) X) = 0 := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [DD.zero_a, DD.epM]
  · funext m
    simp [DD.zero_ep, DD.epM]
  · funext m
    simp [DD.zero_ep', DD.epM]
  · simp [DD.zero_eta, DD.epM]

private theorem epM_neg_transpose {X : Type} [CommRing X] {g n : ℕ} (f : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (fun m => -(f m)ᵀ) = -(DD.epM f)ᵀ := by
  have hn : ∀ y : DD X g, -y = 0 - y := fun y => (zero_sub y).symm
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [DD.neg_a, DD.epM]
  · funext m
    simp [DD.neg_ep, DD.epM]
  · funext m
    have h1 := DD.add_ep' (-(DD.epM f b a)) (DD.epM f b a) m
    rw [neg_add_cancel, DD.zero_ep'] at h1
    simp [DD.epM] at h1 ⊢
  · have h1 := DD.add_eta (-(DD.epM f b a)) (DD.epM f b a)
    rw [neg_add_cancel, DD.zero_eta] at h1
    simp [DD.epM] at h1 ⊢

private theorem one_add_epM_mul_map_C_mul_epM_mul_one_add_epM_mul_map_C {X : Type} [CommRing X] {g n : ℕ} (P P' : Matrix (Fin n) (Fin n) X) (f u u' : Fin g → Matrix (Fin n) (Fin n) X) :
    (1 + DD.epM u) * P.map DD.C * DD.epM f * ((1 + DD.epM u') * P'.map DD.C) = DD.epM (fun m => P * f m * P') := by
  rw [mul_assoc (1 + DD.epM u), map_C_mul_epM, add_mul, one_mul, epM_mul_epM_eq_zero, add_zero, ← mul_assoc,
    mul_add, mul_one, epM_mul_epM_eq_zero, add_zero, epM_mul_map_C]

private theorem map_C_mul_one_add_epM_mul_epM_mul_one_sub_epM_mul_map_C {X : Type} [CommRing X] {g n : ℕ} (P P' : Matrix (Fin n) (Fin n) X) (f u u' : Fin g → Matrix (Fin n) (Fin n) X) :
    P.map DD.C * (1 + DD.epM u) * DD.epM f * ((1 - DD.epM u') * P'.map DD.C) = DD.epM (fun m => P * f m * P') := by
  rw [mul_assoc (P.map DD.C), add_mul, one_mul, epM_mul_epM_eq_zero, add_zero, map_C_mul_epM, ← mul_assoc,
    mul_sub, mul_one, epM_mul_epM_eq_zero, sub_zero, epM_mul_map_C]

private theorem epM_single_map_mem_W1_of_mem_Od {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n : ℕ} (g a : ℕ) (j : Fin g)
    (M : Matrix (Fin n) (Fin n) A) (hM : M ∈ Od A A n a) :
    DD.epM (Pi.single j (M.map (algebraMap A X))) ∈ W1 n A X g a := by
  unfold W1 blkMat ddPart
  unfold Od at hM
  intro r c
  have hrc := hM r c
  refine ⟨fun hd => ?_, fun _ => ?_⟩
  · have h0 : M r c = 0 := by simpa using hrc.1 hd
    refine ⟨fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · funext m
      by_cases hm : m = j
      · subst hm
        simp [DD.epM, h0]
      · simp [DD.epM, Pi.single_apply, hm]
    · funext m
      simp [DD.epM]
    · simp [DD.epM]
  · refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_⟩
    · simp [DD.epM]
    · funext m
      simp [DD.epM]
    · simp [DD.epM]

private theorem adicCont_const_fun {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I (fun _ : Γ => c) := by
  unfold AdicCont
  intro N
  exact IsLocallyConstant.const _

private theorem adicCont_epM_single_map_apply {Γ A X : Type} [TopologicalSpace Γ] [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}
    (t : A) (j : Fin g) (F : Γ → Matrix (Fin n) (Fin n) A) (a b : Fin n)
    (hf : AdicCont (Ideal.span {t}) fun γ => F γ a b) :
    AdicCont (Ideal.span {algebraMap A (DD X g) t}) fun γ => DD.epM (Pi.single j ((F γ).map (algebraMap A X))) a b := by
  set ε : DD X g := DD.epM (Pi.single j (Matrix.of fun _ _ => (1 : X))) a b with hε
  have he : ∀ c : A, ∀ M : Matrix (Fin n) (Fin n) A, M a b = c →
      DD.epM (Pi.single j (M.map (algebraMap A X))) a b = algebraMap A (DD X g) c * ε := by
    intro c M hc
    rw [alg_eq]
    refine DD.ext ?_ ?_ ?_ ?_
    · simp [hε, DD.epM, DD.mul_a, DD.C_a]
    · funext m
      by_cases hm : m = j
      · subst hm
        simp [hε, DD.epM, DD.mul_ep, DD.C_a, DD.C_ep, hc]
      · simp [hε, DD.epM, DD.mul_ep, DD.C_a, DD.C_ep, Pi.single_apply, hm]
    · funext m
      simp [hε, DD.epM, DD.mul_ep', DD.C_a, DD.C_ep']
    · simp [hε, DD.epM, DD.mul_eta, DD.C_eta, DD.C_ep, DD.C_ep']
  unfold AdicCont at hf ⊢
  intro N
  refine (IsLocallyConstant.iff_exists_open _).2 fun γ => ?_
  obtain ⟨U, hU, hγ, hUe⟩ := (IsLocallyConstant.iff_exists_open _).1 (hf N) γ
  refine ⟨U, hU, hγ, fun γ' hγ' => ?_⟩
  have h1 := hUe γ' hγ'
  rw [Ideal.Quotient.eq] at h1 ⊢
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨d, hd⟩ := h1
  beta_reduce at hd ⊢
  rw [he _ (F γ') rfl, he _ (F γ) rfl, ← sub_mul, ← map_sub, hd, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨algebraMap A (DD X g) d * ε, by rw [map_mul, map_pow, mul_assoc]⟩

private theorem bndD_epM_single_map_of_adicCont {Γ A X : Type} [TopologicalSpace Γ] [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}
    (t : A) (j : Fin g) (F : Γ → Matrix (Fin n) (Fin n) A)
    (hf : ∀ a b : Fin n, AdicCont (Ideal.span {t}) fun γ => F γ a b) :
    BndD t fun γ => DD.epM (Pi.single j ((F γ).map (algebraMap A X))) := by
  have hz : BndF t (fun _ : Γ => (0 : X)) :=
    ⟨0, fun _ => 0, adicCont_const_fun _ _, fun _ => by simp⟩
  unfold BndD
  intro a b
  refine ⟨?_, fun m => ?_, fun m => ?_, ?_⟩
  · simpa [DD.epM] using hz
  · by_cases hm : m = j
    · subst hm
      refine ⟨0, fun γ => F γ a b, hf a b, fun γ => ?_⟩
      simp [DD.epM]
    · simpa [DD.epM, Pi.single_apply, hm] using hz
  · simpa [DD.epM] using hz
  · simpa [DD.epM] using hz

private theorem epM_pi_sub {X : Type} [CommRing X] {g n : ℕ} (f f' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (f - f') = DD.epM f - DD.epM f' := by
  rw [eq_sub_iff_add_eq, ← epM_pi_add, sub_add_cancel]

private theorem epM_single_map_apply_eq_zero_of_apply_eq_zero {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ} (j : Fin g)
    (M : Matrix (Fin n) (Fin n) A) (r c : Fin n) (hM : M r c = 0) :
    DD.epM (Pi.single j (M.map (algebraMap A X))) r c = 0 := by
  refine DD.ext ?_ ?_ ?_ ?_
  · simp [DD.epM, DD.zero_a]
  · funext m
    by_cases hm : m = j
    · subst hm
      simp [DD.epM, DD.zero_ep, hM]
    · simp [DD.epM, DD.zero_ep, Pi.single_apply, hm]
  · funext m
    simp [DD.epM, DD.zero_ep']
  · simp [DD.epM, DD.zero_eta]

theorem UpperTheory.V.Pa.kapSel1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ i j : Fin k.g, (fun γ => DD.epM (Pi.single j (kapF h k i γ))) ∈ Sel1 h x.Fr k ∧ BndD x.t fun γ => DD.epM (Pi.single j (kapF h k i γ)) := by
  intro l _ L G G0 h n x k i j
  have hm := k.mem i
  simp only [SelZ, Set.mem_setOf_eq] at hm
  obtain ⟨hOd, hcont, hcoc, hconj, hIu, hloc⟩ := hm
  have hpc : Continuous h.p₀ := Continuous.codRestrict (h.cont.comp continuous_subtype_val) _
  have hc' : ∀ a b : Fin n, AdicCont (Ideal.span {x.t}) fun γ : G.frame.G₀ => k.κ i (h.p₀ γ) a b := by
    intro a b
    have h1 := hcont a b
    rw [Algebra.algebraMap_self, RingHom.id_apply] at h1
    unfold AdicCont at h1 ⊢
    intro N
    exact (h1 N).comp_continuous hpc
  refine ⟨?_, bndD_epM_single_map_of_adicCont x.t j (fun γ => k.κ i (h.p₀ γ)) hc'⟩
  simp only [Sel1, SelZ, Set.mem_setOf_eq]
  refine ⟨fun γ => epM_single_map_mem_W1_of_mem_Od _ _ j _ (hOd _), fun a b => adicCont_epM_single_map_apply x.t j _ a b (hc' a b), fun g g' => ?_,
    fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
  · show DD.epM (Pi.single j ((k.κ i (h.p₀ (g * g'))).map (algebraMap x.A x.Fr))) =
      DD.epM (Pi.single j ((k.κ i (h.p₀ g)).map (algebraMap x.A x.Fr))) +
        k.ρ1 x.Fr (h.p₀ g) * DD.epM (Pi.single j ((k.κ i (h.p₀ g')).map (algebraMap x.A x.Fr))) *
          k.ρ1 x.Fr (h.p₀ g⁻¹)
    rw [map_mul, hcoc, Matrix.map_add _ (map_add _), Pi.single_add, epM_pi_add]
    congr 1
    unfold Kap.ρ1
    rw [show x.ρX (DD x.Fr k.g) (h.p₀ g) = (x.ρX x.Fr (h.p₀ g)).map DD.C from rfl,
      show x.ρX (DD x.Fr k.g) (h.p₀ g⁻¹) = (x.ρX x.Fr (h.p₀ g⁻¹)).map DD.C from rfl, one_add_epM_mul_map_C_mul_epM_mul_one_add_epM_mul_map_C]
    congr 1
    funext m
    by_cases hmj : m = j
    · subst hmj
      simp only [Pi.single_eq_same, map_inv, Matrix.map_mul]
      rfl
    · simp [Pi.single_apply, hmj]
  · have hcj : h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
      apply Subtype.ext
      simp [Glob.Hom.p₀, Glob.frame, GFrame.conj, h.c]
    show DD.epM (Pi.single j ((k.κ i (h.p₀ (G.frame.conj g))).map (algebraMap x.A x.Fr))) =
      -(DD.epM (Pi.single j ((k.κ i (h.p₀ g)).map (algebraMap x.A x.Fr))))ᵀ
    rw [hcj, hconj, ← epM_neg_transpose]
    congr 1
    funext m
    by_cases hmj : m = j
    · subst hmj
      rw [Pi.single_eq_same, Pi.single_eq_same, Matrix.map_neg _ (map_neg _), Matrix.transpose_map]
    · simp [Pi.single_apply, hmj]
  · have hg' : h.p₀ g ∈ Subgroup.map (G0.φu u) (L.Ju u) := by
      obtain ⟨a, ha, rfl⟩ := hg
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      simp [Glob.Hom.p₀, h.φu]
    show DD.epM (Pi.single j ((k.κ i (h.p₀ g)).map (algebraMap x.A x.Fr))) = 0
    rw [hIu u _ hg', Matrix.map_zero _ (map_zero _), Pi.single_zero, epM_pi_zero]
  · obtain ⟨Y, hY, hLY⟩ := hloc v
    refine ⟨DD.epM (Pi.single j (Y.map (algebraMap x.A x.Fr))), epM_single_map_mem_W1_of_mem_Od _ _ j _ hY, ?_⟩
    unfold LocAt at hLY ⊢
    intro gv
    obtain ⟨h1, h2⟩ := hLY gv
    have hφ : h.p₀ ((G.frame.φ v) gv) = (G0.frame.φ v) gv := by
      apply Subtype.ext
      simp [Glob.Hom.p₀, Glob.frame, h.φ]
    have key : k.wi1 x.Fr v * (DD.epM (Pi.single j ((k.κ i (h.p₀ ((G.frame.φ v) gv))).map (algebraMap x.A x.Fr))) -
        dY G.frame (fun g => k.ρ1 x.Fr (h.p₀ g)) (DD.epM (Pi.single j (Y.map (algebraMap x.A x.Fr))))
          ((G.frame.φ v) gv)) * k.w1 x.Fr v =
        DD.epM (Pi.single j ((x.wiX x.A v * (k.κ i ((G0.frame.φ v) gv) - dY G0.frame (x.ρX x.A) Y ((G0.frame.φ v) gv)) *
          x.wX x.A v).map (algebraMap x.A x.Fr))) := by
      unfold dY Kap.ρ1 Kap.wi1 Kap.w1
      beta_reduce
      rw [map_inv, hφ,
        show x.ρX (DD x.Fr k.g) ((G0.frame.φ v) gv) = (x.ρX x.Fr ((G0.frame.φ v) gv)).map DD.C from rfl,
        show x.ρX (DD x.Fr k.g) ((G0.frame.φ v) gv)⁻¹ = (x.ρX x.Fr ((G0.frame.φ v) gv)⁻¹).map DD.C from rfl,
        show x.wiX (DD x.Fr k.g) v = (x.wiX x.Fr v).map DD.C from rfl,
        show x.wX (DD x.Fr k.g) v = (x.wX x.Fr v).map DD.C from rfl,
        one_add_epM_mul_map_C_mul_epM_mul_one_add_epM_mul_map_C, ← epM_pi_sub, ← epM_pi_sub, map_C_mul_one_add_epM_mul_epM_mul_one_sub_epM_mul_map_C]
      congr 1
      funext m
      by_cases hmj : m = j
      · subst hmj
        simp only [Pi.sub_apply, Pi.single_eq_same, Matrix.map_mul, Matrix.map_sub _ (map_sub (algebraMap x.A x.Fr))]
        rfl
      · simp [Pi.single_apply, hmj]
    refine ⟨fun r c hrc => ?_, fun hmu r => ?_⟩
    · show (k.wi1 x.Fr v * (DD.epM (Pi.single j ((k.κ i (h.p₀ ((G.frame.φ v) gv))).map (algebraMap x.A x.Fr))) -
        dY G.frame (fun g => k.ρ1 x.Fr (h.p₀ g)) (DD.epM (Pi.single j (Y.map (algebraMap x.A x.Fr))))
          ((G.frame.φ v) gv)) * k.w1 x.Fr v) r c = 0
      rw [key]
      exact epM_single_map_apply_eq_zero_of_apply_eq_zero j _ r c (h1 r c hrc)
    · show (k.wi1 x.Fr v * (DD.epM (Pi.single j ((k.κ i (h.p₀ ((G.frame.φ v) gv))).map (algebraMap x.A x.Fr))) -
        dY G.frame (fun g => k.ρ1 x.Fr (h.p₀ g)) (DD.epM (Pi.single j (Y.map (algebraMap x.A x.Fr))))
          ((G.frame.φ v) gv)) * k.w1 x.Fr v) r r = 0
      rw [key]
      exact epM_single_map_apply_eq_zero_of_apply_eq_zero j _ r r (h2 hmu r)
