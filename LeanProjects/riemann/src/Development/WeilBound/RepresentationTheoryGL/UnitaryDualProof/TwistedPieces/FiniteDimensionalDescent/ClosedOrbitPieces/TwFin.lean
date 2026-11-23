import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceTop
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.Rdata
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.RqLift

noncomputable section

open Matrix Polynomial Module

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece

open ValuativeRel in

theorem twFin (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p c : ℕ) [Fact p.Prime] [CharP k p] : FiniteDimensional k (Tw k p c) := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  have hc : CompleteSpace k := inferInstance
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  have : CompleteSpace k := hc
  letI : TopologicalSpace (Tw k p c) := inferInstanceAs (TopologicalSpace k)
  have : IsTopologicalAddGroup (Tw k p c) := inferInstanceAs (IsTopologicalAddGroup k)
  have : T2Space (Tw k p c) := inferInstanceAs (T2Space k)
  have : LocallyCompactSpace (Tw k p c) := inferInstanceAs (LocallyCompactSpace k)
  have : ContinuousSMul k (Tw k p c) := ⟨by
    show Continuous fun q : k × k => (iterateFrobenius k p c q.1) * q.2
    simp only [iterateFrobenius_def]
    exact (continuous_fst.pow _).mul continuous_snd⟩
  exact FiniteDimensional.of_locallyCompactSpace k

theorem pad {M : Type*} [AddCommMonoid M] {q d : ℕ} (hqd : q ≤ d) (f : Fin q → M) :
    ∑ l : Fin q, f l = ∑ l : Fin d, if h : (l : ℕ) < q then f ⟨l, h⟩ else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if h : n < q then f ⟨n, h⟩ else 0) d]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 hqd) (fun n _ hn => by
    rw [Finset.mem_range] at hn; rw [dif_neg hn])]
  rw [← Fin.sum_univ_eq_sum_range (fun n => if h : n < q then f ⟨n, h⟩ else 0) q]
  exact Finset.sum_congr rfl fun l _ => by rw [dif_pos l.2]

theorem sect (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Sect k := by
  intro p _ _ N q Z hZ hqc hroots hnilb χ hχm hχd
  obtain ⟨c, rfl⟩ := hqc
  haveI := twFin k p c
  letI : CommRing Z := { (inferInstance : Ring Z) with
    mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }
  haveI : IsReduced Z := hZ.2
  haveI : FiniteDimensional k Z := inferInstance
  haveI := rq_fin (A := Z) χ hχm (p ^ c)
  haveI := rq_pir (A := Z) χ (p ^ c)
  have hnilR : ∀ r : Rq Z χ (p ^ c), IsNilpotent r → r ^ (p ^ c) = 0 := rq_nil χ (p ^ c)
  have hrootR : ∀ a : k, ∃ w : Rq Z χ (p ^ c), w ^ (p ^ c) = algebraMap k _ a := by
    intro a
    obtain ⟨w, hw, hwa⟩ := hroots a
    refine ⟨Ideal.Quotient.mk _ (C ⟨w, hw⟩), ?_⟩
    have h1 : (⟨w, hw⟩ : Z) ^ (p ^ c) = algebraMap k Z a := Subtype.ext (by simpa using hwa)
    rw [← map_pow, ← map_pow, h1]
    rfl
  obtain ⟨r, s, c', u, ε, m, κ, h1, hu, hε, hrep, hid, hsum, horth, hcorner⟩ :=
    rdata (R := Rq Z χ (p ^ c)) p c hnilR hrootR
  have hdN : χ.natDegree ≤ max N (p ^ c) := hχd ▸ le_max_left _ _
  have hdq : p ^ c ≤ max N (p ^ c) := le_max_right _ _
  choose ar har using fun j => rq_rep (A := Z) χ hχm (p ^ c) (max N (p ^ c)) hdN (s j)
  obtain ⟨br, hbr⟩ := rq_rep (A := Z) χ hχm (p ^ c) (max N (p ^ c)) hdN ε
  choose γ0 hγ0 using fun i => hrep (Ideal.Quotient.mk _ (C (Module.finBasis k Z i)))
  obtain ⟨β0, hβ0⟩ := hrep (Ideal.Quotient.mk _ X)
  let ext : (Fin (p ^ c) → Fin r → k) → Fin (max N (p ^ c)) → Fin r → k :=
    fun g l j => if h : (l : ℕ) < p ^ c then g ⟨l, h⟩ j else 0
  let E : Fin m → Rq Z χ (p ^ c) := fun t => ∑ j, κ t j • s j
  refine ⟨{
    r := r
    d := max N (p ^ c)
    a := fun j l => (ar j l : Matrix (Fin N) (Fin N) k)
    ha := fun j l => (ar j l).2
    b := fun l => (br l : Matrix (Fin N) (Fin N) k)
    hb := fun l => (br l).2
    c := c'
    u := u
    a0 := finrank k Z
    z := fun i => (Module.finBasis k Z i : Matrix (Fin N) (Fin N) k)
    hz := ?_
    γ := fun i => ext (γ0 i)
    β := ext β0
    m := m
    κ := κ
    dd := fun t => finrank k (Submodule.span k (Set.range fun j => E t * s j))
    K := fun t => LinearMap.ker ((LinearMap.mulLeft k (E t)).comp (Fintype.linearCombination k s))
    spec := ?_ }⟩
  · apply le_antisymm
    · intro y hy
      have h := congrArg Subtype.val ((Module.finBasis k Z).sum_repr ⟨y, hy⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
      rw [← h]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.span_le.2 (Set.range_subset_iff.2 fun i => (Module.finBasis k Z i).2)
  · intro x hx hχx
    have hB : ∀ P : Z[X], P.eval₂ Z.val.toRingHom x ∈ Bz Z := by
      intro P a ha
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ => rw [eval₂_add, mul_add, add_mul, hP, hQ]
      | monomial n b =>
        rw [eval₂_monomial]
        have e1 : a * (b : Matrix (Fin N) (Fin N) k) = b * a := hZ.1 a ha b b.2
        have e2 : Commute a (x ^ n) := Commute.pow_right (hx a ha) n
        show a * ((b : Matrix (Fin N) (Fin N) k) * x ^ n) = (b : Matrix (Fin N) (Fin N) k) * x ^ n * a
        rw [← mul_assoc, e1, mul_assoc, e2.eq, mul_assoc]
    obtain ⟨ρ, hρ⟩ := rq_lift (A := Z) Z.val x (fun a => hx a a.2) χ hχx (p ^ c)
      (fun P hP => hnilb _ (hB P) hP)
    have hpe : ∀ g : Fin (max N (p ^ c)) → Z, pe (fun l => (g l : Matrix (Fin N) (Fin N) k)) x =
        ρ (Ideal.Quotient.mk _ (∑ l : Fin (max N (p ^ c)), C (g l) * X ^ (l : ℕ))) := by
      intro g
      rw [hρ, eval₂_finset_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul_X_pow_eq_monomial, eval₂_monomial]
      rfl
    have hs : ∀ j, pe (fun l => (ar j l : Matrix (Fin N) (Fin N) k)) x = ρ (s j) := fun j => by
      rw [hpe, ← har j]
    have hε' : pe (fun l => (br l : Matrix (Fin N) (Fin N) k)) x = ρ ε := by rw [hpe, ← hbr]
    have hlin : ∀ v : Fin r → k, ∑ j, v j • ρ (s j) = ρ (∑ j, v j • s j) := fun v => by
      rw [map_sum]; simp only [map_smul]
    have hspan : ∀ y, y ∈ Submodule.span k (Set.range fun j => ρ (s j)) →
        ∃ v : Fin r → k, y = ρ (∑ j, v j • s j) := by
      intro y hy
      obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hy
      exact ⟨v, by rw [← hv, hlin]⟩
    have hE : ∀ t, ∑ j, κ t j • ρ (s j) = ρ (E t) := fun t => hlin (κ t)
    have hsum' : ∑ t, E t = 1 := hsum
    have hid' : ∀ t, IsIdempotentElem (E t) := hid
    have hcor : ∀ t (v : Fin r → k), (∑ j, v j • s j) * E t = 0 ∨
        ∃ w : Rq Z χ (p ^ c), (∑ j, v j • s j) * E t * w = E t := hcorner
    have hre : ∀ g : Fin (p ^ c) → Fin r → k, re (ext g) (fun j => ρ (s j)) (ρ ε) =
        ρ (∑ l, ∑ j, g l j • (s j * ε ^ (l : ℕ))) := by
      intro g
      rw [map_sum, pad hdq]
      unfold re
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : (l : ℕ) < p ^ c
      · rw [dif_pos h, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [ext, dif_pos h, map_smul, map_mul, map_pow]
      · rw [dif_neg h]
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [ext, dif_neg h, zero_smul]
    have nilmul : ∀ a b : Matrix (Fin N) (Fin N) k, Commute a b → IsNilpotent a → IsNilpotent (a * b) :=
      fun a b h ⟨n, hn⟩ => ⟨n, by rw [h.mul_pow, hn, zero_mul]⟩
    have hcomm : ∀ a b : Rq Z χ (p ^ c), Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    dsimp only
    simp only [hs, hε']
    refine ⟨fun j j' => ?_, ?_, fun j j' => ?_, fun j => ?_, ?_, ?_, fun i => ?_, ?_, fun t => ?_, ?_,
      fun t t' htt => ?_, fun t y hy hyi hye => ?_, fun t => ?_, fun v => ?_⟩
    · rw [← map_mul, h1 j j', map_sum]; simp only [map_smul]
    · rw [hlin, hu, map_one]
    · rw [← map_mul, mul_comm, map_mul]
    · rw [← map_mul, mul_comm, map_mul]
    · rw [← map_pow, hε, map_zero]
    · intro y hy hnil
      obtain ⟨v, rfl⟩ := hspan y hy
      have hz0 : ∀ t, ρ ((∑ j, v j • s j) * E t) = 0 := by
        intro t
        rcases hcor t v with h | ⟨w', hw'⟩
        · rw [h, map_zero]
        · have hEn : IsNilpotent (ρ (E t)) := by
            rw [← hw', mul_assoc, map_mul]
            exact nilmul _ _ (hcomm _ _) hnil
          have hE0 : ρ (E t) = 0 := by
            obtain ⟨n, hn⟩ := hEn
            have := ((hid' t).map ρ).pow_succ_eq n
            rw [pow_succ, hn, zero_mul] at this
            exact this.symm
          rw [← (hid' t).eq, ← mul_assoc, map_mul, hE0, mul_zero]
      rw [← mul_one (∑ j, v j • s j), ← hsum', Finset.mul_sum, map_sum]
      exact Finset.sum_eq_zero fun t _ => hz0 t
    · rw [hre, ← hγ0 i, hρ, eval₂_C]
      rfl
    · rw [hre, ← hβ0, hρ, eval₂_X]
    · rw [hE]; exact (hid' t).map ρ
    · simp only [hE]; rw [← map_sum, hsum', map_one]
    · rw [hE, hE, ← map_mul, horth t t' htt, map_zero]
    · rw [hE] at hye ⊢
      obtain ⟨v, rfl⟩ := hspan y hy
      rcases hcor t v with h | ⟨w', hw'⟩
      · left; rw [← hye, ← map_mul, h, map_zero]
      · right
        have e1 : ρ (E t) = ρ (∑ j, v j • s j) * ρ (E t) * ρ w' := by rw [← map_mul, ← map_mul, hw']
        rw [hye] at e1
        calc ρ (∑ j, v j • s j) = ρ (∑ j, v j • s j) * ρ (E t) := hye.symm
          _ = ρ (∑ j, v j • s j) * (ρ (∑ j, v j • s j) * ρ w') := by rw [← e1]
          _ = ρ (∑ j, v j • s j) * ρ w' := by rw [← mul_assoc, hyi.eq]
          _ = ρ (E t) := e1.symm
    · have hfun : (fun j => (∑ j', κ t j' • pe (fun l => (ar j' l : Matrix (Fin N) (Fin N) k)) x) *
          pe (fun l => (ar j l : Matrix (Fin N) (Fin N) k)) x) = fun j => ρ (E t) * ρ (s j) := by
        funext j; simp only [hs, hE]
      have hE2 : ∑ j, κ t j • pe (fun l => (ar j l : Matrix (Fin N) (Fin N) k)) x = ρ (E t) := by
        simp only [hs, hE]
      rw [hfun, hE2]
      have hmap : Submodule.span k (Set.range fun j => ρ (E t) * ρ (s j)) =
          (Submodule.span k (Set.range fun j => E t * s j)).map ρ.toLinearMap := by
        rw [Submodule.map_span, ← Set.range_comp]
        congr 1
        ext j
        simp [map_mul]
      split_ifs with h0
      · have : (fun j => ρ (E t) * ρ (s j)) = fun _ => 0 := by funext j; rw [h0, zero_mul]
        rw [this, Submodule.span_eq_bot.2 (by rintro _ ⟨j, rfl⟩; rfl), finrank_bot]
      · rw [hmap]
        set V := Submodule.span k (Set.range fun j => E t * s j)
        have hinj : Function.Injective (ρ.toLinearMap.comp V.subtype) := by
          rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
          rintro ⟨y, hyV⟩ hy0
          obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hyV
          have hy2 : y = (∑ j, v j • s j) * E t := by
            rw [← hv, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_mul_assoc, mul_comm]
          have hy0' : ρ y = 0 := hy0
          rcases hcor t v with h | ⟨w', hw'⟩
          · exact Subtype.ext (show y = 0 by rw [hy2, h])
          · exact absurd (by rw [← hw', map_mul, ← hy2, hy0', zero_mul]) h0
        rw [← LinearMap.finrank_range_of_inj hinj, LinearMap.range_comp, Submodule.range_subtype]
    · simp only [hE, hlin, LinearMap.mem_ker, LinearMap.comp_apply, Fintype.linearCombination_apply,
        LinearMap.mulLeft_apply]
      constructor
      · intro h0 t hEt
        rcases hcor t v with h | ⟨w', hw'⟩
        · rw [mul_comm]; exact h
        · exact absurd (by rw [← hw', map_mul, map_mul, h0, zero_mul, zero_mul]) hEt
      · intro h
        rw [← mul_one (∑ j, v j • s j), ← hsum', Finset.mul_sum, map_sum]
        refine Finset.sum_eq_zero fun t _ => ?_
        by_cases hEt : ρ (E t) = 0
        · rw [map_mul, hEt, mul_zero]
        · rw [mul_comm, h t hEt, map_zero]

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
