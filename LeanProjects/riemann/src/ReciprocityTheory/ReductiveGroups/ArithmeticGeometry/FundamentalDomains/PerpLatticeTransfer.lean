import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpBasisExistence

namespace ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)

lemma span_L' : Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro x hx
  have h1 : (X.NA : E) • x ∈ Submodule.span E (X.L' : Set (Fin r → E)) :=
    Submodule.subset_span (X.NA_sub x hx)
  have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
  have h2 := Submodule.smul_mem _ ((X.NA : E)⁻¹) h1
  rwa [smul_smul, inv_mul_cancel₀ hNA, one_smul] at h2

variable {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E)

lemma smul_O_E (a : 𝓞 E) (x : E) : a • x = (a : E) * x := by
  rw [Algebra.smul_def]

def Tmap : ((Fin n → E) × E) →ₗ[𝓞 E] (Fin r → E) where
  toFun p := ∑ k, p.1 k • β k + p.2 • ξ
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' a p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    rw [integer_smul_eq_coe_smul a p.1, integer_smul_eq_coe_smul a (∑ k, p.1 k • β k + p.2 • ξ), smul_O_E]
    simp only [Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, mul_smul]

lemma LB_eq : LBsub X β ξ = (X.L'.comap (Tmap β ξ)).map (LinearMap.fst (𝓞 E) (Fin n → E) E) := by
  ext c
  change (∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L') ↔
    c ∈ (X.L'.comap (Tmap β ξ)).map (LinearMap.fst (𝓞 E) (Fin n → E) E)
  simp only [Submodule.mem_map, Submodule.mem_comap, LinearMap.fst_apply, Prod.exists]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨c, e, he, rfl⟩
  · rintro ⟨c', e, hp, rfl⟩
    exact ⟨e, hp⟩

lemma Tmap_inj (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E)) :
    Function.Injective (Tmap β ξ) := by
  intro p q hpq
  have e1 : ∑ k, p.1 k • β k + p.2 • ξ = ∑ k, q.1 k • β k + q.2 • ξ := hpq
  rw [← sub_eq_zero] at e1
  have h := Fintype.linearIndependent_iff.mp hli
    (Fin.cons (p.2 - q.2) (p.1 - q.1) : Fin (n + 1) → E) (by
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.sub_apply, sub_smul,
        Finset.sum_sub_distrib]
      rw [← e1]
      abel)
  refine Prod.ext (funext fun k => ?_) ?_
  · have h' := h k.succ
    simp only [Fin.cons_succ, Pi.sub_apply] at h'
    exact sub_eq_zero.mp h'
  · have h' := h 0
    simp only [Fin.cons_zero] at h'
    exact sub_eq_zero.mp h'

lemma LB_lattice (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E)) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (LBsub X β ξ) := by
  refine ⟨?_, ?_⟩
  · rw [LB_eq]
    apply Submodule.FG.map
    apply Submodule.fg_of_fg_map_injective (Tmap β ξ) (Tmap_inj β ξ hli)
    rw [Submodule.map_comap_eq]
    have : IsNoetherian (𝓞 E) X.L' := isNoetherian_of_fg_of_noetherian _ X.L'_fg
    have h1 := IsNoetherian.noetherian ((LinearMap.range (Tmap β ξ) ⊓ X.L').comap X.L'.subtype)
    have h2 := h1.map X.L'.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr inf_le_right] at h2
  · rw [eq_top_iff]
    intro c _
    obtain ⟨d, hd, hdv⟩ := HermitianTraceFormVanishing.exists_smul_mem (F := E) X.L' (x := ∑ k, c k • β k)
      (by rw [span_L' X]; trivial)
    have hd' : (d : E) ≠ 0 := by simpa using hd
    have hdc : (d : E) • c ∈ LBsub X β ξ := by
      refine ⟨0, ?_⟩
      rw [zero_smul, add_zero]
      have e1 : ∑ k, ((d : E) • c) k • β k = d • ∑ k, c k • β k := by
        rw [integer_smul_eq_coe_smul d, Finset.smul_sum]
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
      rw [e1]
      exact hdv
    have h2 := Submodule.smul_mem (Submodule.span E (LBsub X β ξ : Set (Fin n → E))) ((d : E)⁻¹)
      (Submodule.subset_span hdc)
    rwa [smul_smul, inv_mul_cancel₀ hd', one_smul] at h2

def Sform : ReciprocityTheory.MultiplicativeHeights.HermForm E n where
  c := (IsCMField.complexConj E).toRingEquiv.toRingHom
  c_invol x := IsCMField.complexConj_apply_apply E x
  c_emb σ x := IsCMField.complexEmbedding_complexConj E σ x
  G := Matrix.of fun a b => herm X.Gm (β b) (β a)
  G_herm a b := HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm (β b) (β a)

private lemma herm_sum_smul_left' {m : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : Fin m → E)
    (v : Fin m → Fin r → E) (y : Fin r → E) :
    herm G (∑ k, c k • v k) y = ∑ k, c k * herm G (v k) y := by
  unfold herm
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * v k a * G a b * cc (y b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, c k * v k a * G a b * cc (y b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

private lemma herm_sum_smul_right' {m : ℕ} (G : Matrix (Fin r) (Fin r) E) (x : Fin r → E)
    (c : Fin m → E) (v : Fin m → Fin r → E) :
    herm G x (∑ k, c k • v k) = ∑ k, cc (c k) * herm G x (v k) := by
  unfold herm cc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, x a * G a b * ((IsCMField.complexConj E) (c k) *
        (IsCMField.complexConj E) (v k b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, x a * G a b * ((IsCMField.complexConj E) (c k) *
        (IsCMField.complexConj E) (v k b)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

lemma Sform_h (c c' : Fin n → E) :
    (Sform X β).h c c' = herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k) := by
  rw [herm_sum_smul_left']
  simp only [herm_sum_smul_right', Finset.mul_sum]
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Sform, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  try simp only [cc, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.coe_ringEquiv]
  ring

lemma herm_perp (hβξ : ∀ k, herm X.Gm (β k) ξ = 0) (c : Fin n → E) :
    herm X.Gm (∑ k, c k • β k) ξ = 0 := by
  rw [herm_sum_smul_left']
  simp [hβξ]

private lemma herm_add_left_of_matrix (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  unfold herm
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma herm_add_right_of_matrix (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  unfold herm cc
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private lemma herm_smul_left_of_matrix (G : Matrix (Fin r) (Fin r) E) (e : E) (x y : Fin r → E) :
    herm G (e • x) y = e * herm G x y := by
  unfold herm
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma herm_smul_right_lemma_6 (G : Matrix (Fin r) (Fin r) E) (e : E) (x y : Fin r → E) :
    herm G x (e • y) = cc e * herm G x y := by
  unfold herm cc
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma herm_cross (hβξ : ∀ k, herm X.Gm (β k) ξ = 0) (hξξ : herm X.Gm ξ ξ = 0)
    (c c' : Fin n → E) (e e' : E) :
    herm X.Gm (∑ k, c' k • β k + e' • ξ) (∑ k, c k • β k + e • ξ) =
      herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k) := by
  have hξβ : ∀ k, herm X.Gm ξ (β k) = 0 := fun k => by
    have h := HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm (β k) ξ
    rw [hβξ k] at h
    first
    | simpa [cc] using h
    | simpa [cc] using h.symm
  have hB : herm X.Gm ξ (∑ k, c k • β k) = 0 := by
    rw [herm_sum_smul_right']
    simp [hξβ]
  rw [herm_add_left_of_matrix, herm_add_right_of_matrix, herm_add_right_of_matrix, herm_smul_left_of_matrix,
    herm_smul_left_of_matrix, herm_smul_right_lemma_6, herm_smul_right_lemma_6, hB, herm_perp X β ξ hβξ c', hξξ]
  ring

lemma LB_selfDual (hξ : X.IsIso ξ) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin n → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    ReciprocityTheory.MultiplicativeHeights.IsSelfDual (Sform X β) (LBsub X β ξ) := by
  refine ⟨?_, ?_⟩
  · rintro c ⟨e, he⟩ c' ⟨e', he'⟩
    rw [Sform_h, ← herm_cross X β ξ hβξ hξ.2.1 c c' e e']
    exact ⟨⟨_, X.L'_int _ he' _ he⟩, rfl⟩
  · intro c hc
    obtain ⟨e, he⟩ := hermitian_lattice_pairing_duality r X ξ hξ (∑ k, c k • β k) (herm_perp X β ξ hβξ c) (by
      intro y hy hyξ
      obtain ⟨c', e', rfl⟩ := hspan y hyξ
      have hc' : c' ∈ LBsub X β ξ := ⟨e', hy⟩
      obtain ⟨z, hz⟩ := hc c' hc'
      rw [Sform_h] at hz
      have h1 : herm X.Gm (∑ k, c k • β k) (∑ k, c' k • β k + e' • ξ) =
          cc (herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k)) := by
        rw [herm_add_right', HermitianTraceFormVanishing.herm_smul_right, herm_perp X β ξ hβξ c, mul_zero, add_zero,
          HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm]
      rw [h1, ← hz]
      exact isIntegral_cc (RingOfIntegers.isIntegral_coe z))
    exact ⟨e, he⟩

lemma detG_ne (hξ : X.IsIso ξ) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin n → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    (Sform X β).G.det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hcG⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set μ := ∑ a, cc (c a) • β a with hμdef
  have hβμ : ∀ b, herm X.Gm (β b) μ = 0 := by
    intro b
    have h1 := congrFun hcG b
    simp only [Matrix.vecMul, dotProduct, Sform, Matrix.of_apply, Pi.zero_apply] at h1
    rw [hμdef, herm_sum_right']
    simp only [HermitianTraceFormVanishing.herm_smul_right, HermitianTraceFormVanishing.cc_cc]
    rw [← h1]
  have hμξ : herm X.Gm ξ μ = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm, hμdef, herm_perp X β ξ hβξ, HermitianTraceFormVanishing.cc_zero]
  have hperp : ∀ y, herm X.Gm y ξ = 0 → herm X.Gm μ y = 0 := by
    intro y hy
    obtain ⟨c', e', rfl⟩ := hspan y hy
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm, HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hμξ,
      herm_sum_left']
    simp only [HermitianTraceFormVanishing.herm_smul_left, hβμ, mul_zero, Finset.sum_const_zero, add_zero,
      HermitianTraceFormVanishing.cc_zero]
  obtain ⟨e, he⟩ := HermitianTraceFormVanishing.exists_eq_smul_of_herm X.Gm X.Gm_det X.Gm_herm ξ μ hξ.2.2 hperp
  have h := Fintype.linearIndependent_iff.mp hli (Fin.cons (-e) (fun a => cc (c a))) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    show -e • ξ + μ = 0
    rw [he, neg_smul, neg_add_cancel])
  apply hc0
  funext a
  have := h a.succ
  simpa using this

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
