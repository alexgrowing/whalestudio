import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransferAlt
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IsClosedRank
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Pieces

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP.Desc.Piece.Tr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem tdM : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) := by
  haveI := (tdk : TotallyDisconnectedSpace k)
  exact (inferInstance : TotallyDisconnectedSpace (Fin N → Fin N → k))

theorem comm_span_iff {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    (hb : S.toSubmodule = Submodule.span k (Set.range b)) (y : Matrix (Fin N) (Fin N) k) :
    (∀ a ∈ S, a * y = y * a) ↔ ∀ i, b i * y = y * b i := by
  have hmem : ∀ a, a ∈ S ↔ a ∈ Submodule.span k (Set.range b) := fun a => by
    rw [← hb]; rfl
  constructor
  · exact fun h i => h _ ((hmem _).2 (Submodule.subset_span ⟨i, rfl⟩))
  · intro h a ha
    have key : ∀ a ∈ Submodule.span k (Set.range b), a * y = y * a := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
      | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
    exact key a ((hmem a).1 ha)

theorem cj_eq_self_iff (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : cj g x = x ↔ x * g.val = g.val * x := by
  unfold cj
  constructor
  · intro h
    calc x * g.val = (↑g * x * ↑g⁻¹) * g.val := by rw [h]
      _ = g.val * x := by simp [mul_assoc]
  · intro h
    rw [← h, mul_assoc, Units.mul_inv, mul_one]

theorem mem_GzS_iff {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    (hb : S.toSubmodule = Submodule.span k (Set.range b)) (g : GL (Fin N) k) :
    g ∈ GzS S ↔ ∀ i, cj g (b i) = b i := by
  exact (show g ∈ GzS S ↔ ∀ a ∈ S, a * g.val = g.val * a from Iff.rfl).trans
    ((comm_span_iff hb _).trans (forall_congr' fun i => (cj_eq_self_iff g (b i)).symm))

def Orb {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) : Set (Fin r → Matrix (Fin N) (Fin N) k) :=
  {w | ∃ g : GL (Fin N) k, ∀ i, w i = cj g (b i)}

theorem self_mem_orb {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) : b ∈ Orb b :=
  ⟨1, fun i => (cj_one _).symm⟩

theorem cj_mem_orb {r : ℕ} {b w : Fin r → Matrix (Fin N) (Fin N) k} (hw : w ∈ Orb b) (g : GL (Fin N) k) :
    (fun i => cj g (w i)) ∈ Orb b := by
  obtain ⟨h, hh⟩ := hw
  exact ⟨g * h, fun i => by show cj g (w i) = _; rw [hh, cj_mul]⟩

abbrev cr_commRing {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hS : CR S) : CommRing S :=
  { (inferInstance : Ring S) with mul_comm := fun a b => Subtype.ext (hS.1 a a.2 b b.2) }

theorem span_top_of {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    (hb : S.toSubmodule = Submodule.span k (Set.range b)) :
    Submodule.span k (Set.range fun i => (⟨b i, by
      show b i ∈ S.toSubmodule; rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : S)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx : (x : Matrix (Fin N) (Fin N) k) ∈ Submodule.span k (Set.range b) := by
    rw [← hb]
    exact x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
  refine (Submodule.mem_span_range_iff_exists_fun k).2 ⟨c, ?_⟩
  apply Subtype.ext
  rw [← hc]
  simp

theorem isClosed_orb (hO : OrbClosed k) {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hS : CR S)
    {b : Fin r → Matrix (Fin N) (Fin N) k} (hb : S.toSubmodule = Submodule.span k (Set.range b)) :
    IsClosed (Orb b) := by
  letI : CommRing S := cr_commRing hS
  haveI : IsReduced S := hS.2
  exact hO N r S hS.2 _ (span_top_of hb) S.val

def actO {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) : MulAction (GL (Fin N) k) (Orb b) where
  smul g w := ⟨fun i => cj g (w.1 i), cj_mem_orb w.2 g⟩
  one_smul w := Subtype.ext (funext fun i => cj_one _)
  mul_smul g h w := Subtype.ext (funext fun i => cj_mul g h _)

theorem continuousSMul_actO {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) :
    @ContinuousSMul (GL (Fin N) k) (Orb b) (actO b).toSMul _ _ := by
  letI := actO b
  refine ⟨?_⟩
  show Continuous (fun p : GL (Fin N) k × Orb b => (⟨fun i => cj p.1 (p.2.1 i), cj_mem_orb p.2.2 p.1⟩ : Orb b))
  have hc : ∀ i : Fin r, Continuous (fun p : GL (Fin N) k × Orb b => cj p.1 (p.2.1 i)) := by
    intro i
    have h1 : Continuous (fun p : GL (Fin N) k × Orb b => p.2.1 i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    have h2 : Continuous (fun p : GL (Fin N) k × Orb b => (p.1, p.2.1 i)) := continuous_fst.prodMk h1
    exact (continuous_cj (n := N)).comp h2
  exact Continuous.subtype_mk (continuous_pi hc) _

theorem isPretransitive_actO {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) :
    @MulAction.IsPretransitive (GL (Fin N) k) (Orb b) (actO b).toSMul := by
  letI := actO b
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := x.2
  obtain ⟨h, hh⟩ := y.2
  refine ⟨h * g⁻¹, Subtype.ext (funext fun i => ?_)⟩
  show cj (h * g⁻¹) (x.1 i) = y.1 i
  rw [hg i, hh i, ← cj_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_orb_homeo (hO : OrbClosed k) {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hS : CR S)
    {b : Fin r → Matrix (Fin N) (Fin N) k} (hb : S.toSubmodule = Submodule.span k (Set.range b)) :
    ∃ e : GL (Fin N) k ⧸ GzS S ≃ₜ Orb b, ∀ g : GL (Fin N) k, ((e g : Orb b) : Fin r → Matrix (Fin N) (Fin N) k) =
      fun i => cj g (b i) := by
  letI := actO b
  haveI := continuousSMul_actO b
  haveI := isPretransitive_actO b
  haveI : LocallyCompactSpace (Orb b) := (isClosed_orb hO hS hb).locallyCompactSpace
  obtain ⟨e, he⟩ := exists_quotient_homeo (G := GL (Fin N) k) (⟨b, self_mem_orb b⟩ : Orb b)
  have hst : MulAction.stabilizer (GL (Fin N) k) (⟨b, self_mem_orb b⟩ : Orb b) = GzS S := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_GzS_iff hb]
    constructor
    · intro h i
      exact congrFun (congrArg Subtype.val h) i
    · intro h
      exact Subtype.ext (funext h)
  have key : ∀ H : Subgroup (GL (Fin N) k),
      MulAction.stabilizer (GL (Fin N) k) (⟨b, self_mem_orb b⟩ : Orb b) = H →
      ∃ e : GL (Fin N) k ⧸ H ≃ₜ Orb b, ∀ g : GL (Fin N) k,
        ((e g : Orb b) : Fin r → Matrix (Fin N) (Fin N) k) = fun i => cj g (b i) := by
    rintro H rfl
    exact ⟨e, fun g => by rw [he g]; rfl⟩
  exact key _ hst

theorem rank_add_of_orth {e f : Matrix (Fin N) (Fin N) k} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) : (e + f).rank = e.rank + f.rank := by
  have hE : (e + f) * e = e := by rw [add_mul, he.eq, hfe, add_zero]
  have hF : (e + f) * f = f := by rw [add_mul, hef, hf.eq, zero_add]
  have hsup : LinearMap.range (e + f).mulVecLin =
      LinearMap.range e.mulVecLin ⊔ LinearMap.range f.mulVecLin := by
    apply le_antisymm
    · rw [Matrix.mulVecLin_add]
      exact LinearMap.range_add_le _ _
    · refine sup_le ?_ ?_
      · conv_lhs => rw [← hE]
        rw [Matrix.mulVecLin_mul]
        exact LinearMap.range_comp_le_range _ _
      · conv_lhs => rw [← hF]
        rw [Matrix.mulVecLin_mul]
        exact LinearMap.range_comp_le_range _ _
  have hinf : LinearMap.range e.mulVecLin ⊓ LinearMap.range f.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    simp only [Submodule.mem_inf, LinearMap.mem_range, Matrix.mulVecLin_apply] at hx
    obtain ⟨⟨u, rfl⟩, ⟨w, hw⟩⟩ := hx
    rw [Submodule.mem_bot]
    have hu : e *ᵥ u = e *ᵥ (e *ᵥ u) := by rw [Matrix.mulVec_mulVec, he.eq]
    rw [hu, ← hw, Matrix.mulVec_mulVec, hef, Matrix.zero_mulVec]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e.mulVecLin) (LinearMap.range f.mulVecLin)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  unfold Matrix.rank
  exact h

theorem rank_sum_orth {ι : Type*} [DecidableEq ι] (e : ι → Matrix (Fin N) (Fin N) k) (he : ∀ t, IsIdempotentElem (e t))
    (ho : ∀ t t', t ≠ t' → e t * e t' = 0) (T : Finset ι) :
    IsIdempotentElem (∑ t ∈ T, e t) ∧ (∑ t ∈ T, e t).rank = ∑ t ∈ T, (e t).rank := by
  refine Finset.induction_on T ?_ ?_
  · refine ⟨?_, ?_⟩ <;> simp [IsIdempotentElem, Matrix.rank_zero]
  · intro a s ha ih
    have h1 : e a * ∑ t ∈ s, e t = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun t ht => ho a t (fun h => ha (by rw [h]; exact ht))
    have h2 : (∑ t ∈ s, e t) * e a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun t ht => ho t a (fun h => ha (by rw [← h]; exact ht))
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨(he a).add ih.1 (by rw [h1, h2, add_zero]), by rw [rank_add_of_orth (he a) ih.1 h1 h2, ih.2]⟩

theorem cr_bot : CR (⊥ : Subalgebra k (Matrix (Fin N) (Fin N) k)) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 ha
    exact Algebra.commutes c b
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨n, hn⟩ := hx
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 x.2
    have hn' : (x : Matrix (Fin N) (Fin N) k) ^ n = 0 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [← hc, ← map_pow] at hn'
    by_cases h0 : c = 0
    · apply Subtype.ext
      rw [← hc, h0, map_zero]
      rfl
    · have h1 : (1 : Matrix (Fin N) (Fin N) k) = 0 := by
        have hcn : c ^ n ≠ 0 := pow_ne_zero _ h0
        calc (1 : Matrix (Fin N) (Fin N) k) = algebraMap k _ ((c ^ n)⁻¹ * c ^ n) := by
              rw [inv_mul_cancel₀ hcn, map_one]
          _ = 0 := by rw [map_mul, hn', mul_zero]
      apply Subtype.ext
      show (x : Matrix (Fin N) (Fin N) k) = 0
      rw [← mul_one (x : Matrix (Fin N) (Fin N) k), h1, mul_zero]

def glEquivBot : GL (Fin N) k ≃ₜ* GzS (⊥ : Subalgebra k (Matrix (Fin N) (Fin N) k)) where
  toFun g := ⟨g, fun a ha => by obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 ha; exact Algebra.commutes c g.val⟩
  invFun g := g.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_id _
  continuous_invFun := continuous_subtype_val

theorem isUnimod_GL (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : PositivityTheory.PfBern.Frob.IsUnimod (GL (Fin N) k) :=
  isUnimod_of_equiv glEquivBot (hU N ⊥ cr_bot)

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
