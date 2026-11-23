import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.MapFloorMono

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev IntAlg (O : Type) [CommRing O] [IsDomain O] (σ : Type*) : Subalgebra O (MvPolynomial σ (KK O)) :=
  (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)).range

theorem X_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ : Type*} (v : σ) : (X v : MvPolynomial σ (KK O)) ∈ IntAlg O σ := by
  exact (AlgHom.mem_range _).mpr ⟨MvPolynomial.X v, by simp⟩

theorem intPol_le (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntPol O σ) :
    P ∈ IntAlg O σ := by
  obtain ⟨Q, hQ⟩ := LinearMap.mem_range.mp h
  exact (AlgHom.mem_range _).mpr ⟨Q, hQ⟩

theorem inA_of_mem (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) :
    InA (O := O) P := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  unfold InA
  intro m
  exact ⟨Q.coeff m, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.coeff_map]⟩

theorem rename_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → τ) {P : MvPolynomial σ (KK O)}
    (h : P ∈ IntAlg O σ) : rename f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  exact (AlgHom.mem_range _).mpr ⟨rename f Q, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_rename]⟩

theorem aeval_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → MvPolynomial τ (KK O))
    (hf : ∀ v, f v ∈ IntAlg O τ) {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) : aeval f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  have e : (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)) Q =
      MvPolynomial.map (algebraMap O (KK O)) Q := rfl
  rw [e, MvPolynomial.aeval_map_algebraMap]
  clear h e
  induction Q using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p v hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hf v)

theorem ssz_le_intAlg (O : Type) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (D : BlockData N) :
    ∀ x ∈ D.SSZ O (r := r), x ∈ IntAlg O (BVar N r D.T.t) := by
  intro x hx
  unfold BlockData.SSZ at hx
  refine Submodule.span_induction (p := fun x _ => x ∈ IntAlg O (BVar N r D.T.t)) ?_ ?_ ?_ ?_ hx
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, _, y, hy, g0, hg0, rfl⟩ := hx
    have hX := fun v => X_mem_intAlg O (σ := BVar N r D.T.t) v
    have hE : ∀ i, D.Ehat O (r := r) i ∈ IntAlg O (BVar N r D.T.t) := fun i => by
      unfold BlockData.Ehat
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    have hP : D.Eplus O (r := r) ∈ IntAlg O (BVar N r D.T.t) := by
      unfold BlockData.Eplus
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem
      ((IntAlg O _).mul_mem ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hE i) _)
        ((IntAlg O _).pow_mem hP _)) ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hX _) _))
      ((IntAlg O _).pow_mem (hX _) _)) (rename_mem_intAlg O _ (intPol_le O hy.2))) (intPol_le O hg0.2)
  · exact (IntAlg O _).zero_mem
  · intro x y _ _ hx hy; exact (IntAlg O _).add_mem hx hy
  · intro a x _ hx; exact (IntAlg O _).smul_mem hx a

theorem symIntAt (C0 CE1 CE2 : ℝ) : SymIntAt C0 CE1 CE2 := by
  intro X _ O _ _ mm β s hs
  apply inA_of_mem
  unfold symFam
  refine (IntAlg O _).prod_mem fun j _ => ?_
  unfold ioBlock
  have hX := fun v => X_mem_intAlg O (σ := (X.TT × Bool) × Fin (X.m + 1)) v
  refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ?_ ?_) ?_
  · unfold digitMon
    exact (IntAlg O _).prod_mem fun i _ => (IntAlg O _).prod_mem fun c _ =>
      (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
  · unfold sTopMon
    refine (IntAlg O _).prod_mem fun i _ => ?_
    split_ifs
    · exact (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
    · exact (IntAlg O _).one_mem
  · have hsj : s j ∈ IntAlg O (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) :=
      ssz_le_intAlg O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)) (s j) (hs j)
    exact aeval_mem_intAlg O _ (fun v => (IntAlg O _).pow_mem (hX _) _) hsj

theorem srcHalf_of' {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc H : ℝ} (hCm : 13 ≤ Cm) (hCt : 30 ≤ Ct)
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (h44 : Lemma44At C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hP : PlaneAt) :
    SrcHalfAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc :=
  srcHalf_of hCm hCt hstd h44 monoAt hP (symIntAt C0 CE1 CE2)

theorem restSrcHalf_of (h44 : BinomialRatioBeyondThreshold) (hP : PlaneAt) :
    TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ct0 : ℝ, 0 < Ct0 ∧ ∀ Ct : ℝ, Ct0 ≤ Ct →
      SrcHalfAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc := by
  have h13 : TransportedAlt fun _ _ _ _ _ _ _ _ Cm _ => (13 : ℝ) ≤ Cm :=
    TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 13) (fun _ _ _ _ _ => 1)
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ => h
  refine TransportedAlt.mono ?_ ((thr_std.and h44).and h13)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨_, hstd⟩, h4⟩, hCm⟩
  exact ⟨30, by norm_num, fun Ct hCt => srcHalf_of' hCm hCt hstd h4 hP⟩

end Formalism.MainNotions.ColumnSystems.Pf
