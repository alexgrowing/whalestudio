import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TraceUnique

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.AC

section
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y]

private lemma lift_comm1 {X : Type} (u : X → Module.End ℂ Y) (z : Module.End ℂ Y)
    (h : ∀ x, Commute (u x) z) (p : FreeAlgebra ℂ X) : Commute (FreeAlgebra.lift ℂ u p) z := by
  induction p using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact Algebra.commutes r z
  | grade1 x => simpa using h x
  | mul a b ha hb => rw [map_mul]; exact ha.mul_left hb
  | add a b ha hb => rw [map_add]; exact ha.add_left hb

private lemma lift_comm2 {X X' : Type} (u : X → Module.End ℂ Y) (v : X' → Module.End ℂ Y)
    (h : ∀ x y, Commute (u x) (v y)) (p : FreeAlgebra ℂ X) (q : FreeAlgebra ℂ X') :
    Commute (FreeAlgebra.lift ℂ u p) (FreeAlgebra.lift ℂ v q) :=
  lift_comm1 u _ (fun x => (lift_comm1 v (u x) (fun y => (h x y).symm) q).symm) p

private lemma lift_conj {X : Type} (u v : X → Module.End ℂ Y) (A : Module.End ℂ Y)
    (h : ∀ x, A * u x = v x * A) (p : FreeAlgebra ℂ X) :
    A * FreeAlgebra.lift ℂ u p = FreeAlgebra.lift ℂ v p * A := by
  induction p using FreeAlgebra.induction with
  | grade0 r => simpa using (Algebra.commutes r A).symm
  | grade1 x => simpa using h x
  | mul a b ha hb => rw [map_mul, map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [map_add, map_add, mul_add, add_mul, ha, hb]

private lemma pullbackSymmetry_lift_map_comm (x x' y c A : Module.End ℂ Y) (hA : A * x' = y * A) (hAA : A * A = 1)
    (h1 : Commute x' c) (h2 : Commute y x) (h3 : Commute y c) :
    LinearMap.trace ℂ Y (x * x' * (c * A)) = LinearMap.trace ℂ Y (x' * x * (c * A)) := by
  have hA' : x' * A = A * y := by
    calc x' * A = A * A * x' * A := by rw [hAA, one_mul]
      _ = A * (A * x') * A := by simp only [mul_assoc]
      _ = A * (y * A) * A := by rw [hA]
      _ = A * y * (A * A) := by simp only [mul_assoc]
      _ = A * y := by rw [hAA, mul_one]
  have e1 : x * x' * (c * A) = (x * c * A) * y := by
    calc x * x' * (c * A) = x * (x' * c) * A := by simp only [mul_assoc]
      _ = x * (c * x') * A := by rw [h1.eq]
      _ = x * c * (x' * A) := by simp only [mul_assoc]
      _ = (x * c * A) * y := by rw [hA']; simp only [mul_assoc]
  have e2 : y * (x * c * A) = (x * c * A) * x' := by
    calc y * (x * c * A) = (y * x) * c * A := by simp only [mul_assoc]
      _ = x * (y * c) * A := by rw [h2.eq]; simp only [mul_assoc]
      _ = x * (c * y) * A := by rw [h3.eq]
      _ = x * c * (y * A) := by simp only [mul_assoc]
      _ = (x * c * A) * x' := by rw [← hA]; simp only [mul_assoc]
  rw [e1, LinearMap.trace_mul_comm, e2, LinearMap.trace_mul_comm]
  simp only [mul_assoc]

private lemma conj_list {I : Type} (u v : I → Module.End ℂ Y) (A : Module.End ℂ Y)
    (h : ∀ i, v i * A = A * u i) (l : List I) :
    (l.map v).prod * A = A * (l.map u).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, ih, ← mul_assoc, h, mul_assoc]
end

private lemma prod_mul_prod {I R : Type} [Monoid R] (u v : I → R) (l : List I) (hl : l.Nodup)
    (h : ∀ i k, i ≠ k → Commute (v i) (u k)) :
    (l.map u).prod * (l.map v).prod = (l.map fun i => u i * v i).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hn := List.nodup_cons.1 hl
    have hc : Commute (v i) (l.map u).prod := Commute.list_prod_right _ _ (by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact h i k (fun e => hn.1 (e ▸ hk)))
    simp only [List.map_cons, List.prod_cons]
    rw [← ih hn.2]
    calc u i * (l.map u).prod * (v i * (l.map v).prod)
        = u i * ((l.map u).prod * v i) * (l.map v).prod := by simp only [mul_assoc]
      _ = u i * (v i * (l.map u).prod) * (l.map v).prod := by rw [hc.eq]
      _ = _ := by simp only [mul_assoc]

private lemma prod_single {I R : Type} [Monoid R] (u : I → R) (i : I) (l : List I) (hl : l.Nodup)
    (hi : i ∈ l) (h : ∀ k, k ≠ i → u k = 1) : (l.map u).prod = u i := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    have hn := List.nodup_cons.1 hl
    simp only [List.map_cons, List.prod_cons]
    by_cases e : j = i
    · subst e
      have : (l.map u).prod = 1 := List.prod_eq_one (by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
        exact h k (fun e => hn.1 (e ▸ hk)))
      rw [this, mul_one]
    · rw [h j e, one_mul]
      exact ih hn.2 ((List.mem_cons.1 hi).resolve_left (Ne.symm e))

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.AC

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.AC in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absCore_pf :
    TraceForm → AbsCore := by
  intro hT I _ J M _ _ _ Y _ _ _ _ α a b A hM hrel haa hab hAA hAb hY
  classical
  have hA : ∀ i p, A * FreeAlgebra.lift ℂ (a i) p = FreeAlgebra.lift ℂ (b i) p * A :=
    fun i p => lift_conj _ _ A (hAb i) p
  have hAB : ∀ i k p q, Commute (FreeAlgebra.lift ℂ (a i) p) (FreeAlgebra.lift ℂ (b k) q) :=
    fun i k p q => lift_comm2 _ _ (hab i k) p q
  have hAC : ∀ i k, i ≠ k → ∀ p q, Commute (FreeAlgebra.lift ℂ (a i) p) (FreeAlgebra.lift ℂ (a k) q) :=
    fun i k h p q => lift_comm2 _ _ (haa i k h) p q
  have hnt : ∀ i, Nontrivial (M i) := by
    intro i
    by_contra hn
    have hs : Subsingleton (M i) := not_nontrivial_iff_subsingleton.1 hn
    have h0 : FreeAlgebra.lift ℂ (α i) (1 : FreeAlgebra ℂ (J i)) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have h1 := hrel i 1 h0
    rw [map_one] at h1
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    exact hy (by simpa using LinearMap.congr_fun h1 y)
  have key : ∀ (x : ∀ i, FreeAlgebra ℂ (J i)) (l : List I), l.Nodup →
      (l.map fun i => (Module.finrank ℂ (M i) : ℂ)).prod *
          LinearMap.trace ℂ Y ((l.map fun i => FreeAlgebra.lift ℂ (a i) (x i)).prod * A) =
        (l.map fun i => LinearMap.trace ℂ (M i) (FreeAlgebra.lift ℂ (α i) (x i))).prod *
          LinearMap.trace ℂ Y A := by
    intro x l
    induction l with
    | nil => intro _; simp
    | cons i l ih =>
      intro hl
      have hn := List.nodup_cons.1 hl
      have ihl := ih hn.2
      have c1 : ∀ p, Commute (FreeAlgebra.lift ℂ (a i) p)
          (l.map fun i => FreeAlgebra.lift ℂ (a i) (x i)).prod := fun p =>
        Commute.list_prod_right _ _ (by
          intro z hz
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hz
          exact hAC i k (fun e => hn.1 (e ▸ hk)) p _)
      have c2 : ∀ p, Commute (FreeAlgebra.lift ℂ (b i) p)
          (l.map fun i => FreeAlgebra.lift ℂ (a i) (x i)).prod := fun p =>
        Commute.list_prod_right _ _ (by
          intro z hz
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hz
          exact (hAB k i _ p).symm)
      haveI := hnt i
      have t := hT (J i) (M i) Y (α i) (a i)
        ((l.map fun i => FreeAlgebra.lift ℂ (a i) (x i)).prod * A) (hM i) (hrel i)
        (fun p p' => pullbackSymmetry_lift_map_comm _ _ (FreeAlgebra.lift ℂ (b i) p') _ A (hA i p') hAA (c1 p')
          (hAB i i p p').symm (c2 p')) (x i)
      simp only [List.map_cons, List.prod_cons]
      rw [mul_assoc (FreeAlgebra.lift ℂ (a i) (x i))]
      generalize (l.map fun i => (Module.finrank ℂ (M i) : ℂ)).prod = D at *
      generalize (l.map fun i => LinearMap.trace ℂ (M i) (FreeAlgebra.lift ℂ (α i) (x i))).prod = T at *
      calc _ = D * ((Module.finrank ℂ (M i) : ℂ) * LinearMap.trace ℂ Y
              (FreeAlgebra.lift ℂ (a i) (x i) * ((l.map fun i => FreeAlgebra.lift ℂ (a i) (x i)).prod * A))) := by ring
        _ = LinearMap.trace ℂ (M i) (FreeAlgebra.lift ℂ (α i) (x i)) * (D * LinearMap.trace ℂ Y
              ((l.map fun i => FreeAlgebra.lift ℂ (a i) (x i)).prod * A)) := by rw [t]; ring
        _ = _ := by rw [ihl]; ring
  have hDne : (∏ i, (Module.finrank ℂ (M i) : ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    haveI := hnt i
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := M i)).ne'
  have key' : ∀ x : ∀ i, FreeAlgebra ℂ (J i), (∏ i, (Module.finrank ℂ (M i) : ℂ)) *
      LinearMap.trace ℂ Y (((Finset.univ : Finset I).toList.map
        fun i => FreeAlgebra.lift ℂ (a i) (x i)).prod * A) =
      (∏ i, LinearMap.trace ℂ (M i) (FreeAlgebra.lift ℂ (α i) (x i))) * LinearMap.trace ℂ Y A := by
    intro x
    have := key x (Finset.univ : Finset I).toList (Finset.nodup_toList _)
    simpa only [Finset.prod_map_toList] using this
  have hPm : ∀ x y : ∀ i, FreeAlgebra ℂ (J i),
      ((Finset.univ : Finset I).toList.map fun i => FreeAlgebra.lift ℂ (a i) (x i)).prod *
        ((Finset.univ : Finset I).toList.map fun i => FreeAlgebra.lift ℂ (a i) (y i)).prod =
      ((Finset.univ : Finset I).toList.map fun i => FreeAlgebra.lift ℂ (a i) ((x * y) i)).prod := by
    intro x y
    rw [prod_mul_prod _ _ _ (Finset.nodup_toList _) (fun i k h => hAC i k h _ _)]
    simp only [Pi.mul_apply, map_mul]
  have hP1 : ((Finset.univ : Finset I).toList.map
      fun i => FreeAlgebra.lift ℂ (a i) ((1 : ∀ i, FreeAlgebra ℂ (J i)) i)).prod = 1 :=
    List.prod_eq_one (by
      intro z hz
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hz
      simp)
  have hPs : ∀ i f, ((Finset.univ : Finset I).toList.map fun k => FreeAlgebra.lift ℂ (a k)
      ((Pi.mulSingle i (FreeAlgebra.ι ℂ f) : ∀ i, FreeAlgebra ℂ (J i)) k)).prod = a i f := by
    intro i f
    rw [prod_single _ i _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ i))
      (fun k hk => by simp [Pi.mulSingle_eq_of_ne hk])]
    simp
  have hbl : ∀ i f, a i f = FreeAlgebra.lift ℂ (a i) (FreeAlgebra.ι ℂ f) := fun i f => by simp
  have hbl' : ∀ i f, b i f = FreeAlgebra.lift ℂ (b i) (FreeAlgebra.ι ℂ f) := fun i f => by simp
  let P : (∀ i, FreeAlgebra ℂ (J i)) → Module.End ℂ Y := fun x =>
    ((Finset.univ : Finset I).toList.map fun i => FreeAlgebra.lift ℂ (a i) (x i)).prod
  have hbP : ∀ i f x, Commute (b i f) (P x) := fun i f x =>
    Commute.list_prod_right _ _ (by
      intro z hz
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hz
      rw [hbl' i f]
      exact (hAB k i _ _).symm)
  let Lin : Submodule ℂ (Module.End ℂ Y) := Submodule.span ℂ
    (Set.range fun xy : (∀ i, FreeAlgebra ℂ (J i)) × (∀ i, FreeAlgebra ℂ (J i)) =>
      P xy.1 * (A * P xy.2 * A))
  let Sg : Set (Module.End ℂ Y) := {z | ∃ i f, z = a i f ∨ z = b i f}
  have hgen : ∀ g ∈ Sg, ∀ w ∈ Lin, g * w ∈ Lin := by
    intro g hg w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hw
      obtain ⟨i, f, rfl | rfl⟩ := hg
      · refine Submodule.subset_span ⟨(Pi.mulSingle i (FreeAlgebra.ι ℂ f) * x, y), ?_⟩
        show P _ * (A * P y * A) = a i f * (P x * (A * P y * A))
        have : P (Pi.mulSingle i (FreeAlgebra.ι ℂ f) * x) = a i f * P x := by
          rw [← hPs i f]
          exact (hPm _ _).symm
        rw [this, mul_assoc]
      · refine Submodule.subset_span ⟨(x, Pi.mulSingle i (FreeAlgebra.ι ℂ f) * y), ?_⟩
        show P x * (A * P _ * A) = b i f * (P x * (A * P y * A))
        have : P (Pi.mulSingle i (FreeAlgebra.ι ℂ f) * y) = a i f * P y := by
          rw [← hPs i f]
          exact (hPm _ _).symm
        rw [this, ← mul_assoc (b i f), (hbP i f x).eq, mul_assoc (P x)]
        congr 1
        rw [← mul_assoc (b i f), ← mul_assoc (b i f), ← hAb i f]
        simp only [mul_assoc]
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul r u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
  have hsurj := DiscreteGroups.T1.Desc.Swap3.burnside (Algebra.adjoin ℂ Sg).val (by
    intro W hW
    refine hY W fun i f x hx => ⟨?_, ?_⟩
    · exact hW ⟨a i f, Algebra.subset_adjoin ⟨i, f, Or.inl rfl⟩⟩ x hx
    · exact hW ⟨b i f, Algebra.subset_adjoin ⟨i, f, Or.inr rfl⟩⟩ x hx)
  have hall : ∀ z ∈ Algebra.adjoin ℂ Sg, ∀ w ∈ Lin, z * w ∈ Lin := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem g hg => exact hgen g hg
    | algebraMap r =>
      intro w hw
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hw
    | add u v _ _ hu hv =>
      intro w hw
      rw [add_mul]
      exact add_mem (hu w hw) (hv w hw)
    | mul u v _ _ hu hv =>
      intro w hw
      rw [mul_assoc]
      exact hu _ (hv w hw)
  have h1 : (1 : Module.End ℂ Y) ∈ Lin := Submodule.subset_span ⟨(1, 1), by
    show P 1 * (A * P 1 * A) = 1
    have : P 1 = 1 := hP1
    rw [this, one_mul, mul_one, hAA]⟩
  have hLin : ∀ z, z ∈ Lin := fun z => by
    obtain ⟨⟨z', hz'⟩, rfl⟩ := hsurj z
    simpa using hall z' hz' 1 h1
  have htr : LinearMap.trace ℂ Y A ≠ 0 := by
    intro h0
    have hz : ∀ z ∈ Lin, LinearMap.trace ℂ Y (z * A) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨⟨x, y⟩, rfl⟩ := hw
        show LinearMap.trace ℂ Y (P x * (A * P y * A) * A) = 0
        have e : P x * (A * P y * A) * A = (P x * A) * P y := by
          calc P x * (A * P y * A) * A = P x * A * P y * (A * A) := by simp only [mul_assoc]
            _ = _ := by rw [hAA, mul_one]
        rw [e, LinearMap.trace_mul_comm, ← mul_assoc]
        have e2 : P y * P x = P (y * x) := hPm y x
        rw [e2]
        have := key' (y * x)
        rw [h0, mul_zero] at this
        exact (mul_eq_zero.1 this).resolve_left hDne
      | zero => simp
      | add u v _ _ hu hv => rw [add_mul, map_add, hu, hv, add_zero]
      | smul r u _ hu => rw [smul_mul_assoc, map_smul, hu, smul_zero]
    have := hz A (hLin A)
    rw [hAA, LinearMap.trace_one] at this
    exact (Nat.cast_ne_zero.2 (Module.finrank_pos (R := ℂ) (M := Y)).ne') this
  refine ⟨LinearMap.trace ℂ Y A / ∏ i, (Module.finrank ℂ (M i) : ℂ), div_ne_zero htr hDne, fun f g => ?_⟩
  let fi : ∀ i, FreeAlgebra ℂ (J i) := fun i => FreeAlgebra.ι ℂ (f i)
  let gi : ∀ i, FreeAlgebra ℂ (J i) := fun i => FreeAlgebra.ι ℂ (g i)
  have e1 : ((Finset.univ : Finset I).toList.map fun i => a i (f i) * b i (g i)).prod =
      P fi * ((Finset.univ : Finset I).toList.map fun i => b i (g i)).prod := by
    rw [← show ((Finset.univ : Finset I).toList.map fun i => a i (f i)).prod = P fi by
      simp only [P, fi, FreeAlgebra.lift_ι_apply]]
    exact (prod_mul_prod _ _ _ (Finset.nodup_toList _) (fun i k _ => (hab k i _ _).symm)).symm
  have e2 : ((Finset.univ : Finset I).toList.map fun i => b i (g i)).prod * A = A * P gi := by
    have : P gi = ((Finset.univ : Finset I).toList.map fun i => a i (g i)).prod := by
      simp only [P, gi, FreeAlgebra.lift_ι_apply]
    rw [this]
    exact conj_list _ _ A (fun i => (hAb i (g i)).symm) _
  have e3 : LinearMap.trace ℂ Y (((Finset.univ : Finset I).toList.map
      fun i => a i (f i) * b i (g i)).prod * A) = LinearMap.trace ℂ Y (P (gi * fi) * A) := by
    rw [e1, mul_assoc, e2, ← mul_assoc, LinearMap.trace_mul_comm, ← mul_assoc]
    have : P gi * P fi = P (gi * fi) := hPm gi fi
    rw [this]
  have e4 := key' (gi * fi)
  have e5 : ∀ i, LinearMap.trace ℂ (M i) (FreeAlgebra.lift ℂ (α i) ((gi * fi) i)) =
      LinearMap.trace ℂ (M i) (α i (f i) * α i (g i)) := by
    intro i
    simp only [gi, fi, Pi.mul_apply, map_mul, FreeAlgebra.lift_ι_apply]
    exact LinearMap.trace_mul_comm _ _ _
  simp only [e5] at e4
  rw [e3]
  change _ * LinearMap.trace ℂ Y (P (gi * fi) * A) = _ at e4
  field_simp
  rw [mul_comm, e4, mul_comm]
