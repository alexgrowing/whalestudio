import Mathlib
import Formalism.LocalToGlobal.Columns.AtTLemmas

open Module

noncomputable section

namespace Formalism.L2.Col

namespace RamFun

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, CommGroup (G i)]
  [∀ i, Fintype (G i)] {M : Type} [AddCommGroup M] [Module K M]

variable (K M) in

def trl (b : ∀ i, G i) : Module.End K ((∀ i, G i) → M) := LinearMap.funLeft K M fun c => b * c

theorem trl_apply (b : ∀ i, G i) (F : (∀ i, G i) → M) (c : ∀ i, G i) : trl K M b F c = F (b * c) := rfl

theorem trl_one : trl K M (1 : ∀ i, G i) = 1 := by
  refine LinearMap.ext fun F => funext fun c => ?_
  show F (1 * c) = F c
  rw [one_mul]

theorem trl_mul (b b' : ∀ i, G i) : trl K M b * trl K M b' = trl K M (b * b') := by
  refine LinearMap.ext fun F => funext fun c => ?_
  show F (b' * (b * c)) = F (b * b' * c)
  congr 1
  rw [mul_left_comm, mul_assoc]

theorem trl_comm (b b' : ∀ i, G i) : Commute (trl K M b) (trl K M b') := by
  show trl K M b * trl K M b' = trl K M b' * trl K M b
  rw [trl_mul, trl_mul, mul_comm]

variable (K M) in

def nmF (i : ι) : Module.End K ((∀ i, G i) → M) := ∑ g : G i, trl K M (Pi.mulSingle i g)

variable (K M G) in

def ramFun : Submodule K ((∀ i, G i) → M) := ⨅ i, LinearMap.ker (nmF K M (G := G) i)

variable (K M G) in

def offAlg (i : ι) : Submodule K (Module.End K ((∀ i, G i) → M)) :=
  Submodule.span K {x | ∃ b : ∀ i, G i, b i = 1 ∧ x = trl K M b}

theorem one_mem_offAlg (i : ι) : (1 : Module.End K ((∀ i, G i) → M)) ∈ offAlg K G M i := by
  have h : trl K M (1 : ∀ i, G i) ∈ offAlg K G M i := Submodule.subset_span ⟨1, rfl, rfl⟩
  rwa [trl_one] at h

theorem mul_mem_offAlg (i : ι) {x y : Module.End K ((∀ i, G i) → M)} (hx : x ∈ offAlg K G M i)
    (hy : y ∈ offAlg K G M i) : x * y ∈ offAlg K G M i := by
  unfold offAlg at *
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨b, hb, rfl⟩ := hx'
      obtain ⟨b', hb', rfl⟩ := hy'
      exact Submodule.subset_span ⟨b * b', by rw [Pi.mul_apply, hb, hb', one_mul], trl_mul b b'⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

theorem nmF_mem_offAlg {i j : ι} (h : j ≠ i) : nmF K M (G := G) j ∈ offAlg K G M i := by
  unfold nmF
  exact Submodule.sum_mem _ fun g _ =>
    Submodule.subset_span ⟨Pi.mulSingle j g, Pi.mulSingle_eq_of_ne h.symm g, rfl⟩

theorem nmF_comm_trl (i : ι) (b : ∀ i, G i) : Commute (nmF K M (G := G) i) (trl K M b) :=
  Commute.sum_left _ _ _ fun _ _ => trl_comm _ _

theorem nmF_comm (i j : ι) : Commute (nmF K M (G := G) i) (nmF K M (G := G) j) :=
  Commute.sum_left _ _ _ fun _ _ => (nmF_comm_trl j _).symm

theorem nmF_sq (i : ι) : nmF K M (G := G) i * nmF K M i = (Fintype.card (G i) : K) • nmF K M i := by
  have key : ∀ g : G i, nmF K M (G := G) i * trl K M (Pi.mulSingle i g) = nmF K M i := by
    intro g
    show (∑ h : G i, trl K M (Pi.mulSingle i h)) * trl K M (Pi.mulSingle i g) =
      ∑ h : G i, trl K M (Pi.mulSingle i h)
    rw [Finset.sum_mul]
    simp_rw [trl_mul, ← Pi.mulSingle_mul]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun _ => rfl
  calc nmF K M (G := G) i * nmF K M i = ∑ g : G i, nmF K M (G := G) i * trl K M (Pi.mulSingle i g) := by
        rw [← Finset.mul_sum]; rfl
    _ = ∑ _g : G i, nmF K M (G := G) i := Finset.sum_congr rfl fun g _ => key g
    _ = (Fintype.card (G i) : K) • nmF K M i := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K]

section Trace

variable [FiniteDimensional K M]

theorem trace_trl {b : ∀ i, G i} (hb : b ≠ 1) : LinearMap.trace K _ (trl K M b) = 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basis fun _ : (∀ i, G i) => Module.finBasis K M), Matrix.trace]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨c, k⟩ := p
  have hc : b * c ≠ c := fun h => hb (mul_right_cancel (h.trans (one_mul c).symm))
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr, trl_apply]
  rw [Pi.single_eq_of_ne hc]
  simp

theorem trace_mul_offAlg {i : ι} {g : G i} (hg : g ≠ 1) {x : Module.End K ((∀ i, G i) → M)}
    (hx : x ∈ offAlg K G M i) : LinearMap.trace K _ (trl K M (Pi.mulSingle i g) * x) = 0 := by
  unfold offAlg at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [trl_mul]
    refine trace_trl fun h => hg ?_
    have := congrFun h i
    simpa [hb] using this
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [mul_smul_comm, map_smul, hx, smul_zero]

theorem trace_nmF_mul {i : ι} {x : Module.End K ((∀ i, G i) → M)} (hx : x ∈ offAlg K G M i) :
    LinearMap.trace K _ (nmF K M i * x) = LinearMap.trace K _ x := by
  show LinearMap.trace K _ ((∑ g : G i, trl K M (Pi.mulSingle i g)) * x) = _
  rw [Finset.sum_mul, map_sum, Finset.sum_eq_single (1 : G i)]
  · rw [Pi.mulSingle_one, trl_one, one_mul]
  · intro g _ hg
    exact trace_mul_offAlg hg hx
  · intro h
    exact absurd (Finset.mem_univ _) h

end Trace

end RamFun

namespace RamFun

section Proj

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
  [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] {M : Type} [AddCommGroup M] [Module K M]

variable (K M G) in

def eF (i : ι) : Module.End K ((∀ i, G i) → M) := 1 - ((Fintype.card (G i) : K)⁻¹) • nmF K M i

theorem card_ne (i : ι) : (Fintype.card (G i) : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem nmF_mul_eF (i : ι) : nmF K M i * eF K G M i = 0 := by
  unfold eF
  rw [mul_sub, mul_one, mul_smul_comm, nmF_sq, smul_smul, inv_mul_cancel₀ (card_ne (K := K) (G := G) i),
    one_smul, sub_self]

theorem eF_mem_offAlg {i j : ι} (h : j ≠ i) : eF K G M j ∈ offAlg K G M i :=
  Submodule.sub_mem _ (one_mem_offAlg i) (Submodule.smul_mem _ _ (nmF_mem_offAlg h))

theorem nmF_comm_eF (i j : ι) : Commute (nmF K M (G := G) i) (eF K G M j) :=
  (Commute.one_right _).sub_right ((nmF_comm i j).smul_right _)

variable (K M G) in

def eL (l : List ι) : Module.End K ((∀ i, G i) → M) := (l.map (eF K G M)).prod

theorem eL_mem_offAlg {i : ι} {l : List ι} (h : i ∉ l) : eL K G M l ∈ offAlg K G M i := by
  induction l with
  | nil =>
    simp only [eL, List.map_nil, List.prod_nil]
    exact one_mem_offAlg i
  | cons a l ih =>
    rw [List.mem_cons, not_or] at h
    simp only [eL, List.map_cons, List.prod_cons] at ih ⊢
    exact mul_mem_offAlg i (eF_mem_offAlg (Ne.symm h.1)) (ih h.2)

theorem nmF_mul_eL {i : ι} {l : List ι} (h : i ∈ l) : nmF K M i * eL K G M l = 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [eL, List.map_cons, List.prod_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h'
    · rw [← mul_assoc, nmF_mul_eF, zero_mul]
    · rw [← mul_assoc, (nmF_comm_eF i a).eq, mul_assoc, ih h', mul_zero]

theorem eL_fix {F : (∀ i, G i) → M} (hF : F ∈ ramFun K G M) (l : List ι) : eL K G M l F = F := by
  have h1 : ∀ j, eF K G M j F = F := by
    intro j
    have h0 : nmF K M j F = 0 := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hF j)
    simp [eF, h0]
  induction l with
  | nil => simp [eL]
  | cons a l ih =>
    simp only [eL, List.map_cons, List.prod_cons] at ih ⊢
    show eF K G M a ((List.map (eF K G M) l).prod F) = F
    rw [ih, h1]

variable [FiniteDimensional K M]

theorem trace_eL {l : List ι} (hl : l.Nodup) :
    LinearMap.trace K _ (eL K G M l) =
      (l.map fun i => (1 - (Fintype.card (G i) : K)⁻¹)).prod * LinearMap.trace K ((∀ i, G i) → M) 1 := by
  induction l with
  | nil => simp [eL]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hx : eL K G M l ∈ offAlg K G M a := eL_mem_offAlg hl.1
    have e : eL K G M (a :: l) = eF K G M a * eL K G M l := by simp [eL]
    rw [e, eF, sub_mul, one_mul, smul_mul_assoc, map_sub, map_smul, trace_nmF_mul hx, ih hl.2,
      List.map_cons, List.prod_cons, smul_eq_mul]
    ring

theorem isProj_eL : LinearMap.IsProj (ramFun K G M) (eL K G M Finset.univ.toList) where
  map_mem F := by
    refine (Submodule.mem_iInf _).2 fun i => ?_
    show nmF K M i (eL K G M Finset.univ.toList F) = 0
    rw [← Module.End.mul_apply, nmF_mul_eL (Finset.mem_toList.2 (Finset.mem_univ i))]
    rfl
  map_id F hF := eL_fix hF _

theorem finrank_ramFun : finrank K (ramFun K G M) = finrank K M * ∏ i, (Fintype.card (G i) - 1) := by
  have h := (isProj_eL (K := K) (G := G) (M := M)).trace
  rw [trace_eL (Finset.nodup_toList _), LinearMap.trace_one, Finset.prod_map_toList] at h
  have hV : finrank K ((∀ i, G i) → M) = (∏ i, Fintype.card (G i)) * finrank K M := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_pi, smul_eq_mul]
  have hc : ∀ i, ((Fintype.card (G i) - 1 : ℕ) : K) =
      (Fintype.card (G i) : K) * (1 - (Fintype.card (G i) : K)⁻¹) := by
    intro i
    rw [Nat.cast_sub (Fintype.card_pos : 1 ≤ Fintype.card (G i)), Nat.cast_one, mul_sub, mul_one,
      mul_inv_cancel₀ (card_ne (K := K) (G := G) i)]
  rw [hV] at h
  apply Nat.cast_injective (R := K)
  rw [← h]
  simp only [Nat.cast_mul, Nat.cast_prod]
  rw [Finset.prod_congr rfl fun i _ => hc i, Finset.prod_mul_distrib]
  ring

end Proj

end RamFun

section ColsRank

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

instance colDiaComm (u : Pr.Word) (j : ℕ) :
    SMulCommClass (DiaG X.E (Pr.vT u)) (colGSD W Ch u j).G (colGSD W Ch u j).D :=
  ⟨fun c a d => DecoSet.dia_smul c (FormG.incl (colLev Ch j) a) d⟩

theorem colDiaFree (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    (colGSD W Ch u 0).FreeOnCl (DiaG X.E (Pr.vT u)) := by
  intro c d h
  obtain ⟨a, ha⟩ := ((colGSD W Ch u 0).cls_eq_iff _ _).1 h
  have hpos : 0 < (Pr.vG 0).card := by
    rw [hPr.vG_card 0, Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hw' : w ∈ Pr.vGs := by
    classical
    unfold Primes.vGs
    exact Finset.mem_union_left _ hw
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hmem : (a.2 : GLG X.E (R.N 0) Pr.vGs) ⟨w, hw'⟩ ∈ (colLev Ch 0 ⟨w, hw'⟩).H :=
    (Subgroup.mem_pi _).mp a.2.2 ⟨w, hw'⟩ (Set.mem_univ _)
  rw [colLev_of_lt Ch hm] at hmem
  exact DecoSet.dia_free_cols hX hPr (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs)
    (a := FormG.incl (colLev Ch 0) a) (c := c) ha 0 ⟨w, hw'⟩ hw (by rw [hN]; exact hbig)
    (isNilpotent_of_mem_HX_zero hN.le hmem)

@[reducible] def fintypeResU (P : HeightOneSpectrum (𝓞 X.E)) : Fintype (𝓞 X.E ⧸ P.asIdeal)ˣ := Fintype.ofFinite _

open Classical in

theorem split_NmOp (u : Pr.Word) (j : ℕ) (σ : (colGSD W Ch u j).Slice (DiaG X.E (Pr.vT u)))
    (P : {P // P ∈ Pr.vT u}) (φ : ColV W Ch u j) :
    letI : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
    σ.split (NmOp W Ch u j P φ) = RamFun.nmF X.K _ P (σ.split φ) := by
  letI : Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fintypeResU P.1
  have e : ∀ (x : DiaG X.E (Pr.vT u)) (d : (colGSD W Ch u j).D), x • d = DecoSet.dia x d := fun _ _ => rfl
  have hc : ∀ c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ,
      σ.split (diamondOperatorOnForms' (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P c φ) =
        RamFun.trl X.K _ (Pi.mulSingle P c) (σ.split φ) := by
    intro c
    funext b
    apply Subtype.ext
    funext t
    simp only [diamondOperatorOnForms', LocOp.op, LocOp.ofMap, LocOp.app, GSD.Slice.split, RamFun.trl_apply,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finsupp.sum_single_index (by simp)]
    simp only [LinearMap.id_apply, DecoSet.dia1]
    congr 1
    rw [e, e, DecoSet.dia_mul]
  have hN : NmOp W Ch u j P φ = ∑ c, diamondOperatorOnForms' (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P c φ := by
    simp only [NmOp, NmG, LinearMap.sum_apply]
  rw [hN, map_sum]
  simp only [hc]
  show _ = (∑ g, RamFun.trl X.K _ (Pi.mulSingle P g)) (σ.split φ)
  rw [LinearMap.sum_apply]

theorem card_resU (hPr : Pr.Ok) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Nat.card (𝓞 X.E ⧸ P.1.asIdeal)ˣ = Pr.T u - 1 := by
  haveI := P.1.isMaximal
  letI := Ideal.Quotient.field P.1.asIdeal
  rw [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hPr.vT_norm u P.1 P.2]

open Classical in

theorem finrank_ColRamV_of_slice (hX : X.Ok) (u : Pr.Word) (j : ℕ)
    (σ : (colGSD W Ch u j).Slice (DiaG X.E (Pr.vT u))) :
    finrank X.K (ColRamV W Ch u j) = finrank X.K ((colGSD W Ch u j).restr σ.T).EqFun *
      ∏ P : {P // P ∈ Pr.vT u}, (Nat.card (𝓞 X.E ⧸ P.1.asIdeal)ˣ - 1) := by
  letI : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
  have hok : (colGSD W Ch u j).Ok := formGSD_ok _ _ hX (colVal_eqv W hX u j _ _)
  haveI : FiniteDimensional X.K ((colGSD W Ch u j).restr σ.T).EqFun :=
    GSD.finiteDimensional_EqFun (h := GSD.restr_ok (h := hok) (T := σ.T))
  have key : ColRamV W Ch u j = (RamFun.ramFun X.K (fun P : {P // P ∈ Pr.vT u} => (𝓞 X.E ⧸ P.1.asIdeal)ˣ)
      ((colGSD W Ch u j).restr σ.T).EqFun).comap σ.split.toLinearMap := by
    ext φ
    simp only [ColRamV, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_comap, RamFun.ramFun]
    refine forall_congr' fun P => ?_
    rw [LinearEquiv.coe_coe, ← split_NmOp W Ch u j σ P φ, LinearEquiv.map_eq_zero_iff]
  rw [key, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, RamFun.finrank_ramFun]
  simp only [Nat.card_eq_fintype_card]

open Classical in

theorem finrank_ColV_of_slice (hX : X.Ok) (u : Pr.Word) (j : ℕ)
    (σ : (colGSD W Ch u j).Slice (DiaG X.E (Pr.vT u))) :
    finrank X.K (ColV W Ch u j) = finrank X.K ((colGSD W Ch u j).restr σ.T).EqFun *
      ∏ P : {P // P ∈ Pr.vT u}, Nat.card (𝓞 X.E ⧸ P.1.asIdeal)ˣ := by
  letI : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
  have hok : (colGSD W Ch u j).Ok := formGSD_ok _ _ hX (colVal_eqv W hX u j _ _)
  haveI : FiniteDimensional X.K ((colGSD W Ch u j).restr σ.T).EqFun :=
    GSD.finiteDimensional_EqFun (h := GSD.restr_ok (h := hok) (T := σ.T))
  rw [σ.split.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_pi, mul_comm]
  simp only [Nat.card_eq_fintype_card]

theorem finrank_MramV_mul (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    finrank X.K (MramV W Ch u) * (Pr.T u - 1) ^ X.f = finrank X.K (MfV W Ch u) * (Pr.T u - 2) ^ X.f := by
  classical
  obtain ⟨σ⟩ := GSD.exists_slice (hf := colDiaFree W Ch hX hPr hbig u)
  have h1 := finrank_ColRamV_of_slice W Ch hX u 0 σ
  have h2 := finrank_ColV_of_slice W Ch hX u 0 σ
  simp only [card_resU hPr u] at h1 h2
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPr.vT_card u] at h1 h2
  show finrank X.K (ColRamV W Ch u 0) * _ = finrank X.K (ColV W Ch u 0) * _
  have e : Pr.T u - 1 - 1 = Pr.T u - 2 := by omega
  rw [h1, h2, e]
  ring

theorem finrank_MramV_pos (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (hT : 2 < Pr.T u) : 0 < finrank X.K (MramV W Ch u) := by
  have h := finrank_MramV_mul W Ch hX hPr hbig u
  have hM := finrank_MfV_pos W Ch hX hPr hbig u
  have hpos : 0 < finrank X.K (MfV W Ch u) * (Pr.T u - 2) ^ X.f :=
    Nat.mul_pos hM (pow_pos (by omega) _)
  rw [← h] at hpos
  exact Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hpos; exact lt_irrefl 0 hpos

end ColsRank

end Formalism.L2.Col
