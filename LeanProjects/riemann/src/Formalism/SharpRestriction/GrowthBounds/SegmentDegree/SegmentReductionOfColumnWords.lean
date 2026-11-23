import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNeZeroOfResidueNeZero

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def ColumnWordReductionLifts (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ) (e : ℤ × Fin (r + K) →₀ ℕ), X.IsEll p K j e → X.Step2 p K j b →
    ∀ q ∈ segPairs X.F j K (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j),
    ∀ I' I'', IsSt q.1 I' → IsSt q.2 I'' →
      ∃ x ∈ X.XXs p K O j, MvPolynomial.map (IsLocalRing.residue O) x =
        MvPolynomial.map (IsLocalRing.residue O)
          (X.zSeg p K O j (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) e)

theorem map_suppProj {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (s : Set (σ →₀ ℕ))
    (A : MvPolynomial σ R) : MvPolynomial.map f (suppProj R s A) = suppProj S s (MvPolynomial.map f A) := by
  classical
  ext m
  rw [coeff_map, coeff_suppProj, coeff_suppProj, coeff_map]
  split_ifs <;> simp

theorem plEmb_Pol {R : Type} [CommRing R] (r K : ℕ) {d : ℤ → ℕ} {A : MvPolynomial (ℤ × Fin r) R}
    (hA : A ∈ Pol R r d) : plEmb R r K A ∈ Pol R (r + K) d := by
  classical
  have hf : Function.Injective (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)
  rw [mem_Pol_iff] at hA ⊢
  intro m hm i
  unfold plEmb at hm
  rw [support_rename_of_injective hf] at hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  rw [← hA u hu i]
  unfold multideg
  rw [Fin.sum_univ_add]
  have z1 : ∀ c : Fin r, Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) u (i, Fin.castAdd K c)
      = u (i, c) := fun c => Finsupp.mapDomain_apply hf u (i, c)
  have z2 : ∀ c : Fin K, Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) u (i, Fin.natAdd r c)
      = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [Prod.mk.injEq] at hv
    have := congrArg Fin.val hv.2
    simp at this
    omega
  simp only [z1, z2, Finset.sum_const_zero, add_zero]

theorem nmEmb_Pol {R : Type} [CommRing R] (r K : ℕ) {d : ℤ → ℕ} {A : MvPolynomial (ℤ × Fin K) R}
    (hA : A ∈ Pol R K d) : nmEmb R r K A ∈ Pol R (r + K) d := by
  classical
  have hf : Function.Injective (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.natAdd_injective _ _ h.2)
  rw [mem_Pol_iff] at hA ⊢
  intro m hm i
  unfold nmEmb at hm
  rw [support_rename_of_injective hf] at hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  rw [← hA u hu i]
  unfold multideg
  rw [Fin.sum_univ_add]
  have z1 : ∀ c : Fin K, Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) u (i, Fin.natAdd r c)
      = u (i, c) := fun c => Finsupp.mapDomain_apply hf u (i, c)
  have z2 : ∀ c : Fin r, Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) u (i, Fin.castAdd K c)
      = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [Prod.mk.injEq] at hv
    have := congrArg Fin.val hv.2
    simp at this
    omega
  simp only [z1, z2, Finset.sum_const_zero, zero_add]

theorem geR_mono {v v' : WithTop ℤ} {t : ℝ} (h : geR v t) (hv : v ≤ v') : geR v' t := by
  intro z hz
  rw [hz] at hv
  induction v using WithTop.recTopCoe with
  | top => simp at hv
  | coe z0 =>
    have h1 : z0 ≤ z := WithTop.coe_le_coe.mp hv
    exact (h z0 rfl).trans (by exact_mod_cast h1)

theorem XX'_polComp (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K] {n' : ℕ} [NeZero n'] (F : Frames n' r)
    (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ) (β : ℤ → ℕ) {x : SegRing O r K} (hx : x ∈ XX' O r K F j m th o) :
    polComp O (r + K) β x ∈ XX' O r K F j m th o := by
  classical
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  have hx2' := hx2
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · clear hx hx2 hx2'
    induction hx1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨A, G, M, hA, hG, hc, rfl⟩ := hy
      obtain ⟨T', hT'⟩ := exists_sum_polComp O r A
      obtain ⟨T'', hT''⟩ := exists_sum_polComp O K G
      have hsum : plEmb O r K A * nmEmb O r K G = ∑ d' ∈ T', ∑ d'' ∈ T'',
          plEmb O r K (polComp O r d' A) * nmEmb O r K (polComp O K d'' G) := by
        conv_lhs => rw [hT', hT'']
        rw [map_sum, map_sum, Finset.sum_mul_sum]
      rw [hsum, map_sum]
      refine Submodule.sum_mem _ fun d' _ => ?_
      rw [map_sum]
      refine Submodule.sum_mem _ fun d'' _ => ?_
      have hP : plEmb O r K (polComp O r d' A) * nmEmb O r K (polComp O K d'' G) ∈ Pol O (r + K) (d' + d'') :=
        hom_Pol_mul O (plEmb_Pol r K (polComp_mem_Pol O r d' A)) (nmEmb_Pol r K (polComp_mem_Pol O K d'' G))
      by_cases hd : β = d' + d''
      · rw [hd, polComp_of_mem O _ _ _ hP]
        refine Submodule.subset_span ⟨_, _, M, polComp_mem_supported O r d' A _ hA,
          polComp_mem_supported O K d'' G _ hG, fun x hx hW => ?_, rfl⟩
        obtain ⟨cE, cO, cR⟩ := hc x hx hW
        exact ⟨fun he => ⟨(lowest_degree_compose_le _ _ d'' G).trans (cE he).1, (cE he).2.trans (valS_le_polComp _ _ d' A)⟩,
          fun he => ⟨(lowest_degree_compose_le _ _ d'' G).trans (cO he).1, (cO he).2.trans (valS_le_polComp _ _ d' A)⟩,
          geR_mono cR (valS_le_polComp _ _ d' A)⟩
      · rw [polComp_of_ne O _ _ _ _ hP hd]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  · rw [mem_restrictSupport_iff] at hx2 ⊢
    intro mm hmm
    exact hx2 (Finset.mem_coe.mpr (suppProj_support_subset O _ x (Finset.mem_coe.mp hmm)))

theorem zSeg_add {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ)
    (y1 y2 : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) :
    X.zSeg p K O j (y1 + y2) e = X.zSeg p K O j y1 e + X.zSeg p K O j y2 e := by
  unfold Dat.zSeg; rw [map_add]; ring

theorem zSeg_smul {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ) (c : O)
    (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) :
    X.zSeg p K O j (c • y) e = c • X.zSeg p K O j y e := by
  unfold Dat.zSeg; rw [map_smul, mul_smul_comm, smul_mul_assoc]

theorem segment_reduction_of_column_words (D : Formalism.BasicNotions.D7) (hB12 : NestedTypeBound D) (C₀ : ℝ) (hW : ColumnWordReductionLifts C₀) : SegmentReductionLiftsMultihomogeneous C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b y e hy he h2 β hβ
  have : Fact p.Prime := ⟨hX.prime⟩
  have hseg : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h1 := (hB12 p O S n' r K X.F X.L₁ X.N₁ j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) hX.valid hseg
    (fun _ => Int.natCast_nonneg _)).1
  have hy1 : y ∈ XX' O r K X.F j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) := hy.1.1
  rw [h1] at hy1
  unfold Formalism.MainNotions.CovariantDegrees.XXZ at hy1
  rw [Submodule.map_span] at hy1
  have key : ∃ x ∈ X.XXs p K O j, MvPolynomial.map (IsLocalRing.residue O) x =
      MvPolynomial.map (IsLocalRing.residue O) (X.zSeg p K O j y e) := by
    clear hβ hy
    induction hy1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩ := hy
      exact hW p n' r K X O S hX hLa hk j b e he h2 q hq I' I'' hI' hI''
    | zero => exact ⟨0, Submodule.zero_mem _, by simp [Dat.zSeg]⟩
    | add y z _ _ hy hz =>
      obtain ⟨x1, hx1, e1⟩ := hy
      obtain ⟨x2, hx2, e2⟩ := hz
      exact ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, by rw [zSeg_add, map_add, map_add, e1, e2]⟩
    | smul c y _ hy =>
      obtain ⟨x1, hx1, e1⟩ := hy
      refine ⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩
      rw [zSeg_smul, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, e1]
  obtain ⟨x, hx, hxe⟩ := key
  refine ⟨polComp O (r + K) β x, XX'_polComp O r K X.F j _ _ _ β hx, polComp_mem_Pol O _ β x, ?_⟩
  unfold polComp
  rw [map_suppProj, hxe, ← map_suppProj]
  congr 1
  exact polComp_of_mem O _ β _ hβ

end Formalism.MainNotions.SelectionLemmas.Pf
