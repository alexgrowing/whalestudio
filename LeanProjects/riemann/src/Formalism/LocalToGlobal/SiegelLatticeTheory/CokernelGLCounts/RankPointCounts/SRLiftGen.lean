import Mathlib

noncomputable section

namespace Formalism.L2.SG.Pf.SRL

open Matrix Module

section Compl

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem exists_isCompl_mem {U : Submodule k V} {e : V} (h : Disjoint U (k ∙ e)) :
    ∃ C : Submodule k V, IsCompl U C ∧ e ∈ C := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (U ⊔ k ∙ e)
  refine ⟨k ∙ e ⊔ W, ⟨h.disjoint_sup_right_of_disjoint_sup_left hW.disjoint, ?_⟩,
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self e)⟩
  rw [codisjoint_iff, ← sup_assoc]
  exact hW.sup_eq_top

theorem exists_isCompl_le {R' K : Submodule k V} (h : R' ⊔ K = ⊤) : ∃ W : Submodule k V, IsCompl R' W ∧ W ≤ K := by
  obtain ⟨W0, hW0⟩ := Submodule.exists_isCompl (R' ⊓ K)
  refine ⟨W0 ⊓ K, ⟨?_, ?_⟩, inf_le_right⟩
  · rw [disjoint_iff, eq_bot_iff, ← hW0.inf_eq_bot]
    exact le_inf (inf_le_inf_left _ inf_le_right) (inf_le_right.trans inf_le_left)
  · have hm : (R' ⊓ K) ⊔ (W0 ⊓ K) = K := by
      rw [← sup_inf_assoc_of_le W0 (inf_le_right : R' ⊓ K ≤ K), hW0.sup_eq_top, top_inf_eq]
    rw [codisjoint_iff, eq_top_iff, ← h]
    refine sup_le le_sup_left ?_
    calc K = (R' ⊓ K) ⊔ (W0 ⊓ K) := hm.symm
      _ ≤ R' ⊔ (W0 ⊓ K) := sup_le_sup_right inf_le_left _

end Compl

section Field

variable {k : Type*} [Field k] {n : ℕ}

theorem srLift_field (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (K : Submodule k (Fin (n + 1) → k))
    (hA : ∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0)
    (hK : ∀ v, ∃ x, v - A *ᵥ x ∈ K) :
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) k, (∀ j, (fun i => H i j) ∈ K) ∧ (∀ i, H i (Fin.last n) = 0) ∧
      (A + H).det ≠ 0 := by
  classical
  have he : A *ᵥ Pi.single (Fin.last n) 1 = Pi.single (Fin.last n) 1 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hA]
  have hRK : LinearMap.range A.mulVecLin ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, hx⟩ := hK v
    rw [show v = A *ᵥ x + (v - A *ᵥ x) by abel]
    exact Submodule.add_mem_sup (LinearMap.mem_range.2 ⟨x, Matrix.mulVecLin_apply A x⟩) hx
  obtain ⟨W, hW, hWK⟩ := exists_isCompl_le hRK
  have hdisj : Disjoint (LinearMap.ker A.mulVecLin) (k ∙ (Pi.single (Fin.last n) 1 : Fin (n + 1) → k)) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx2
    rw [LinearMap.mem_ker, map_smul, Matrix.mulVecLin_apply, he] at hx1
    exact hx1
  obtain ⟨C, hC, heC⟩ := exists_isCompl_mem hdisj
  have hdim : finrank k (LinearMap.ker A.mulVecLin) = finrank k W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    omega
  let φ := LinearEquiv.ofFinrankEq _ _ hdim
  let h : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k) :=
    W.subtype ∘ₗ φ.toLinearMap ∘ₗ (LinearMap.ker A.mulVecLin).projectionOnto C hC
  have hHv : ∀ v, LinearMap.toMatrix' h *ᵥ v = h v := fun v => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  refine ⟨LinearMap.toMatrix' h, fun j => ?_, fun i => ?_, ?_⟩
  · have hc : (fun i => LinearMap.toMatrix' h i j) = h (Pi.single j 1) := by
      funext i
      rw [LinearMap.toMatrix'_apply]
    rw [hc]
    exact hWK (φ _).2
  · have h0 : (LinearMap.ker A.mulVecLin).projectionOnto C hC (Pi.single (Fin.last n) 1) = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hC ⟨_, heC⟩
    rw [LinearMap.toMatrix'_apply]
    simp [h, h0]
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hv0
    rw [Matrix.add_mulVec, hHv] at hv
    have hvt : v ∈ LinearMap.ker A.mulVecLin ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, c, hc, rfl⟩ := Submodule.mem_sup.1 hvt
    have hfx : A *ᵥ x = 0 := by
      rw [← Matrix.mulVecLin_apply]
      exact LinearMap.mem_ker.1 hx
    have hproj : (LinearMap.ker A.mulVecLin).projectionOnto C hC (x + c) = ⟨x, hx⟩ := by
      rw [map_add, Submodule.linearProjOfIsCompl_apply_left hC ⟨x, hx⟩,
        Submodule.linearProjOfIsCompl_apply_right hC ⟨c, hc⟩, add_zero]
    have hv' : A *ᵥ c + (φ ⟨x, hx⟩ : Fin (n + 1) → k) = 0 := by
      have e : h (x + c) = (φ ⟨x, hx⟩ : Fin (n + 1) → k) := by
        simp only [h, LinearMap.comp_apply, hproj]
        rfl
      rw [Matrix.mulVec_add, hfx, zero_add, e] at hv
      exact hv
    have hz : A *ᵥ c = 0 := by
      refine Submodule.disjoint_def.1 hW.disjoint _
        (LinearMap.mem_range.2 ⟨c, Matrix.mulVecLin_apply A c⟩) ?_
      rw [eq_neg_of_add_eq_zero_left hv']
      exact W.neg_mem (φ _).2
    have hφ : φ ⟨x, hx⟩ = 0 := by
      rw [hz, zero_add] at hv'
      exact Subtype.ext hv'
    have hx0 : x = 0 := by
      have := congrArg Subtype.val (φ.map_eq_zero_iff.1 hφ)
      simpa using this
    have hc0 : c = 0 := Submodule.disjoint_def.1 hC.disjoint c
      (LinearMap.mem_ker.2 (by rw [Matrix.mulVecLin_apply]; exact hz)) hc
    rw [hx0, hc0, add_zero]

end Field

section Semilocal

variable {R : Type*} [CommRing R] {n : ℕ}

def redV (m : Ideal R) (v : Fin (n + 1) → R) : Fin (n + 1) → R ⧸ m := fun i => Ideal.Quotient.mk m (v i)

def Kbar (m : Ideal R) [m.IsMaximal] (K : Submodule R (Fin (n + 1) → R)) :
    letI := Ideal.Quotient.field m; Submodule (R ⧸ m) (Fin (n + 1) → R ⧸ m) :=
  letI := Ideal.Quotient.field m
  { carrier := redV m '' (K : Set (Fin (n + 1) → R))
    add_mem' := by
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, K.add_mem ha hb, by funext i; simp [redV]⟩
    zero_mem' := ⟨0, K.zero_mem, by funext i; simp [redV]⟩
    smul_mem' := by
      rintro c _ ⟨a, ha, rfl⟩
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨c' • a, K.smul_mem c' ha, by funext i; simp [redV]⟩ }

theorem exists_local (m : Ideal R) [hm : m.IsMaximal] (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (K : Submodule R (Fin (n + 1) → R)) (hA : ∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0)
    (hK : ∀ v, ∃ x, v - A *ᵥ x ∈ K) :
    ∃ G : Matrix (Fin (n + 1)) (Fin (n + 1)) R, (∀ j, (fun i => G i j) ∈ K) ∧ (∀ i, G i (Fin.last n) = 0) ∧
      (A + G).det ∉ m := by
  classical
  letI := Ideal.Quotient.field m
  let Ab : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⧸ m) := A.map (Ideal.Quotient.mk m)
  have hAb : ∀ i, Ab i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
    intro i
    simp only [Ab, Matrix.map_apply, hA i]
    split_ifs <;> simp
  have hKb : ∀ v, ∃ x, v - Ab *ᵥ x ∈ Kbar m K := by
    intro v
    obtain ⟨w, rfl⟩ : ∃ w : Fin (n + 1) → R, redV m w = v :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
        funext fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
    obtain ⟨x, hx⟩ := hK w
    refine ⟨redV m x, ?_⟩
    show _ ∈ redV m '' (K : Set (Fin (n + 1) → R))
    refine ⟨w - A *ᵥ x, hx, ?_⟩
    funext i
    simp [redV, Ab, Matrix.mulVec, dotProduct, map_sum]
  obtain ⟨Hb, hHcol, hHlast, hdet⟩ := srLift_field Ab (Kbar m K) hAb hKb
  have hlift : ∀ j, ∃ g : Fin (n + 1) → R, g ∈ K ∧ redV m g = fun i => Hb i j := by
    intro j
    obtain ⟨g, hg, hge⟩ := hHcol j
    exact ⟨g, hg, hge⟩
  choose g hgK hgr using hlift
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j => if j = Fin.last n then 0 else g j i
  refine ⟨G, fun j => ?_, fun i => by simp [G], ?_⟩
  · by_cases hj : j = Fin.last n
    · simp only [G, hj, if_true]
      exact K.zero_mem
    · simp only [G, hj, if_false]
      exact hgK j
  · intro hmem
    apply hdet
    have e : Ideal.Quotient.mk m (A + G).det = (Ab + Hb).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
      congr 1
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, map_add, Ab]
      congr 1
      by_cases hj : j = Fin.last n
      · subst hj
        rw [hHlast i, show G i (Fin.last n) = 0 from if_pos rfl, map_zero]
      · rw [show G i j = g j i from if_neg hj]
        exact congrFun (hgr j) i
    calc (Ab + Hb).det = Ideal.Quotient.mk m (A + G).det := e.symm
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem

theorem exists_idem (S : Finset (Ideal R)) (hS : ∀ m ∈ S, m.IsMaximal) (m : Ideal R) (hm : m ∈ S) :
    ∃ e : R, e - 1 ∈ m ∧ ∀ m' ∈ S, m' ≠ m → e ∈ m' := by
  classical
  have hb : ∀ m' ∈ S, m' ≠ m → ∃ b, b ∈ m' ∧ b - 1 ∈ m := by
    intro m' hm' hne
    have h1 : (1 : R) ∈ m ⊔ m' := by
      rw [Ideal.IsMaximal.coprime_of_ne (hS m hm) (hS m' hm') (Ne.symm hne)]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨b, hb, ?_⟩
    rw [show b - 1 = -a by rw [← hab]; ring]
    exact m.neg_mem ha
  choose! b hbm hb1 using hb
  refine ⟨∏ m' ∈ S.erase m, b m', ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, map_prod, map_one]
    apply Finset.prod_eq_one
    intro m' hm'
    rw [Finset.mem_erase] at hm'
    rw [Ideal.Quotient.eq.2 (hb1 m' hm'.2 hm'.1), map_one]
  · intro m' hm' hne
    rw [← Finset.mul_prod_erase (S.erase m) b (Finset.mem_erase.2 ⟨hne, hm'⟩)]
    exact Ideal.mul_mem_right _ _ (hbm m' hm' hne)

theorem srLift_of_finite (hfin : {m : Ideal R | m.IsMaximal}.Finite) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (K : Submodule R (Fin (n + 1) → R)) (hA : ∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0)
    (hK : ∀ v, ∃ x, v - A *ᵥ x ∈ K) :
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) R, (∀ j, (fun i => H i j) ∈ K) ∧ (∀ i, H i (Fin.last n) = 0) ∧
      IsUnit (A + H).det := by
  classical
  let S := hfin.toFinset
  have hSm : ∀ m ∈ S, m.IsMaximal := fun m hm => hfin.mem_toFinset.1 hm
  have hloc : ∀ m ∈ S, ∃ G : Matrix (Fin (n + 1)) (Fin (n + 1)) R, (∀ j, (fun i => G i j) ∈ K) ∧
      (∀ i, G i (Fin.last n) = 0) ∧ (A + G).det ∉ m := fun m hm => by
    haveI := hSm m hm
    exact exists_local m A K hA hK
  choose! G hGK hGl hGd using hloc
  have hidem : ∀ m ∈ S, ∃ e : R, e - 1 ∈ m ∧ ∀ m' ∈ S, m' ≠ m → e ∈ m' :=
    fun m hm => exists_idem S hSm m hm
  choose! e he1 he0 using hidem
  refine ⟨∑ m ∈ S, e m • G m, fun j => ?_, fun i => ?_, ?_⟩
  · have hc : (fun i => (∑ m ∈ S, e m • G m) i j) = ∑ m ∈ S, e m • fun i => G m i j := by
      funext i
      simp [Matrix.sum_apply, Finset.sum_apply]
    rw [hc]
    exact K.sum_mem fun m hm => K.smul_mem _ (hGK m hm j)
  · rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun m hm => by rw [Matrix.smul_apply, hGl m hm i, smul_zero]
  · by_contra hu
    obtain ⟨M, hM, hdetM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
    have hMS : M ∈ S := hfin.mem_toFinset.2 hM
    apply hGd M hMS
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hdetM ⊢
    rw [RingHom.map_det, RingHom.mapMatrix_apply] at hdetM ⊢
    convert hdetM using 2
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add]
    congr 1
    rw [Matrix.sum_apply, map_sum, Finset.sum_eq_single M]
    · have h1 : Ideal.Quotient.mk M (e M) = 1 := by
        rw [← map_one (Ideal.Quotient.mk M)]
        exact Ideal.Quotient.eq.2 (he1 M hMS)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, h1, one_mul]
    · intro b hb hbM
      rw [Matrix.smul_apply, smul_eq_mul, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 (he0 b hb M hMS (Ne.symm hbM)), zero_mul]
    · intro h
      exact absurd hMS h

end Semilocal

end Formalism.L2.SG.Pf.SRL
