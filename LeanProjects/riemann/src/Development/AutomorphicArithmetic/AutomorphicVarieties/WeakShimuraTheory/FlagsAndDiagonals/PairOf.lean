import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ResFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.UpConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem conj_flag {R : Type} [CommRing R] {m u n b : M4 R} (hm : IsGSp 1 m) (hb : IsGSp 1 b)
    (e : adj m * u = n * b) (X : M4 R) : adj n * (adj m * X * m) * n = b * (adj u * X * u) * adj b := by
  have hmm : ∀ Y : M4 R, m * (adj m * Y) = Y := fun Y => by
    rw [← mul_assoc, sp_mul_adj hm, one_mul]
  have hn : n = adj m * u * adj b := by
    rw [e, mul_assoc, sp_mul_adj hb, mul_one]
  rw [hn, adj_mul, adj_mul, adj_adj, adj_adj]
  simp only [mul_assoc, hmm]

private theorem low_mem {R : Type} [CommRing R] {I : Ideal R} {n : M4 R} (hn : IsLow n) (h10 : n 1 0 ∈ I) (h30 : n 3 0 ∈ I)
    (h21 : n 2 1 ∈ I) : ∀ i j, i ≠ j → wt i j ≠ -wPs → n i j ∈ I := by
  intro i j hij hw
  have hup : ∀ i j : Fin 4, i < j → n i j ∈ I := fun i j h => by
    rw [hn.2.2 i j h]
    exact I.zero_mem
  have hsp := congrFun (congrFun (sp_adj_mul hn.1) 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, hn.2.1, hn.2.2, UpperTheory.V.GradeZeroInterpolatingElement.sgn] at hsp
  have h32 : n 3 2 ∈ I := by
    have : n 3 2 = -n 1 0 := by linear_combination hsp
    rw [this]
    exact I.neg_mem h10
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact hup _ _ (by decide)
    | exact h10
    | exact h30
    | exact h21
    | exact h32
    | exact absurd (by simp [UpperTheory.V.GradeZeroInterpolatingElement.wt, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.lamW, UpperTheory.V.GradeZeroInterpolatingElement.muW]) hw

private theorem ps_chi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
    (𝔞 : Amb l) {pr : Bool} (h : LabOk D pr) {s : G ℚ Ω} (hs : s ∈ D.Gp l) (i : Fin 4) :
    𝔞.a c (D.ps i s) - 𝔞.a c (chi D pr i s) ∈ maximalIdeal 𝔞.V := by
  haveI := 𝔞.loc c
  cases pr with
  | false =>
    have : chi D false i s = D.ps i s := rfl
    rw [this, sub_self]
    exact Ideal.zero_mem _
  | true =>
    have hbar : Raw.bar D.Psi s = 1 := h rfl s hs
    have hP : (↑(D.Psi s) : c.O) - 1 ∈ maximalIdeal c.O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one]
      have hb : residue c.O ↑(D.Psi s) = 1 := hbar
      rw [hb, sub_self]
    have hPm := map_nonunit (𝔞.a c) _ hP
    have key : ∀ x : (c.O)ˣ, 𝔞.a c ↑(x * D.Psi s) - 𝔞.a c ↑x ∈ maximalIdeal 𝔞.V := by
      intro x
      have e : 𝔞.a c (↑x * ↑(D.Psi s)) - 𝔞.a c ↑x = 𝔞.a c ↑x * 𝔞.a c (↑(D.Psi s) - 1) := by
        rw [map_mul, map_sub, map_one]
        ring
      rw [Units.val_mul, e]
      exact Ideal.mul_mem_left _ _ hPm
    have key' : ∀ x : (c.O)ˣ, 𝔞.a c ↑x - 𝔞.a c ↑(x * D.Psi s) ∈ maximalIdeal 𝔞.V := by
      intro x
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 (key x)
    fin_cases i
    · show 𝔞.a c ↑(D.th s) - 𝔞.a c ↑(D.al s) ∈ _
      have : D.th s = D.al s * D.Psi s := rfl
      rw [this]
      exact key _
    · show 𝔞.a c ↑(D.Psi s) - 𝔞.a c ↑((1 : G ℚ Ω →* (c.O)ˣ) s) ∈ _
      have : D.Psi s = (1 : G ℚ Ω →* (c.O)ˣ) s * D.Psi s := by simp
      rw [this]
      exact key _
    · show 𝔞.a c ↑(D.al s) - 𝔞.a c ↑(D.th s) ∈ _
      have : D.th s = D.al s * D.Psi s := rfl
      rw [this]
      exact key' _
    · show 𝔞.a c ↑((1 : G ℚ Ω →* (c.O)ˣ) s) - 𝔞.a c ↑(D.Psi s) ∈ _
      have : D.Psi s = (1 : G ℚ Ω →* (c.O)ˣ) s * D.Psi s := by simp
      rw [this]
      exact key' _

theorem UpperTheory.V.Ws.Lab.pairOf :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u →
      ∀ (pr : Bool) (g0 : G ℚ Ω) (P : PD Unit (G ℚ Ω) 𝔞.V) (v b : M4 𝔞.V), LabOk D pr → 𝔞.Small P → IsGSp 1 v → Cg (maximalIdeal 𝔞.V) v 1 →
      (∀ g, P.r g = adj (wM 𝔞.V pr * v) * r g * (wM 𝔞.V pr * v)) → (P.r g0).IsDiag → IsLow (P.n ()) → IsGSp 1 b → IsUp b →
      adj (wM 𝔞.V pr * v) * u = P.n () * b → QPair D pr g0 𝔞 P ∧ NearSplit D pr 𝔞 P := by
  intro Ω _ _ _ l _ c D hG 𝔞 r u hK pr g0 P v b hlab hsmall hv hvc hPr hdiag hlow hb hbup e
  have hMsp : IsGSp 1 (wM 𝔞.V pr * v) := sp_mul (wM_sp pr) hv
  have hwM : ∀ d : Fin 4 → 𝔞.V,
      adj (wM 𝔞.V pr) * Matrix.diagonal d * wM 𝔞.V pr = Matrix.diagonal (fun i => d (lab pr i)) := by
    intro d
    cases pr
    · simp [UpperTheory.V.Ws.wM, UpperTheory.V.Ws.lab, adj_one]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.wM, UpperTheory.V.Ws.lab, Matrix.mul_apply,
        Fin.sum_univ_four, adj_apply, UpperTheory.V.GradeZeroInterpolatingElement.sgn, Matrix.diagonal, Fin.rev]
  have hflag : ∀ s ∈ D.Gp l, IsUp (adj (P.n ()) * P.r s * P.n ()) ∧
      ∀ i, (adj (P.n ()) * P.r s * P.n ()) i i = (adj u * r s * u) i i := by
    intro s hs
    rw [hPr s, conj_flag hMsp hb e (r s)]
    exact upConj 𝔞.V b _ hb hbup (hK.flag s hs)
  have hdr : ∀ (f : Fin 4 → G ℚ Ω →* (c.O)ˣ) (g : G ℚ Ω) (i j : Fin 4),
      𝔞.a c (diagRep f g i j) = Matrix.diagonal (fun i => 𝔞.a c ↑(f i g)) i j := by
    intro f g i j
    unfold UpperTheory.V.GradeZeroInterpolatingElement.diagRep
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  have hred : ∀ g i j, P.r g i j - 𝔞.a c (diagRep (chi D pr) g i j) ∈ maximalIdeal 𝔞.V := by
    intro g
    have hw : Cg (maximalIdeal 𝔞.V) (wM 𝔞.V pr) (wM 𝔞.V pr) := fun i j => by
      rw [sub_self]
      exact Ideal.zero_mem _
    have hM : Cg (maximalIdeal 𝔞.V) (wM 𝔞.V pr * v) (wM 𝔞.V pr * 1) := Cg.mul hw hvc
    rw [mul_one] at hM
    have hR : Cg (maximalIdeal 𝔞.V) (r g) (Matrix.diagonal fun i => 𝔞.a c ↑(D.ps i g)) := by
      intro i j
      have h1 := hK.red g i j
      have h2 : 𝔞.a c (D.r0 g i j) = Matrix.diagonal (fun i => 𝔞.a c ↑(D.ps i g)) i j := by
        unfold UpperTheory.V.GradeZeroInterpolatingElement.Raw.r0
        exact hdr D.ps g i j
      rwa [h2] at h1
    have hC := Cg.mul (Cg.mul (Cg.adj hM) hR) hM
    rw [hwM] at hC
    intro i j
    rw [hdr, hPr g]
    exact hC i j
  obtain ⟨hs, hsep⟩ := sg_sep hG 𝔞 pr
  have hX : Cg (maximalIdeal 𝔞.V) (P.r (D.sg l)) (Matrix.diagonal fun i => 𝔞.a c ↑(chi D pr i (D.sg l))) := by
    intro i j
    have := hred (D.sg l) i j
    rwa [hdr] at this
  obtain ⟨hfl, hdg⟩ := hflag (D.sg l) hs
  have hdiag' : ∀ i, (adj (P.n ()) * P.r (D.sg l) * P.n ()) i i - 𝔞.a c ↑(D.ps i (D.sg l)) ∈ maximalIdeal 𝔞.V := by
    intro i
    rw [hdg i]
    exact hK.char _ hs i
  obtain ⟨h10, h30, -, h4⟩ := resFlag 𝔞.V (P.r (D.sg l)) (P.n ()) (fun i => 𝔞.a c ↑(chi D pr i (D.sg l)))
    (fun i => 𝔞.a c ↑(D.ps i (D.sg l))) hX hlow.1 hfl hdiag' (fun i j h => hsep i j h)
  have h00 : P.n () 0 0 = 1 := hlow.2.1 0
  have h01 : P.n () 0 1 = 0 := hlow.2.2 0 1 (by decide)
  have h21 : P.n () 2 1 ∈ maximalIdeal 𝔞.V := by
    have := (h4 (by rw [h00]; exact isUnit_one)).2
    rwa [h00, h01, one_mul, zero_mul, sub_zero] at this
  refine ⟨⟨hsmall, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ⟨hred, low_mem hlow h10 h30 h21, ?_⟩⟩
  · intro g
    show IsGSp (𝔞.a c ↑(D.th g)) (P.r g)
    rw [hPr g]
    exact gsp_conj hMsp (hK.mult g)
  · intro g hg
    rcases hg with ⟨A, hA, hgA, hr⟩ | ⟨p, hp, hgp⟩
    · rw [hPr g, hK.unr A hA g hgA hr, mul_one, sp_adj_mul hMsp]
    · rw [hPr g, hK.atP p hp g hgp, mul_one, sp_adj_mul hMsp]
  · exact hdiag
  · intro w
    exact hlow
  · intro w s hs'
    exact (hflag s hs').1
  · intro w s hs'
    exact absurd hs' (Set.notMem_empty s)
  · intro s hs' i
    have hs'' : s ∈ D.Gp l := Ine_le_Dec (F := ℚ) (D.pl l) hs'
    show (adj (P.n ()) * P.r s * P.n ()) i i = _
    rw [(hflag s hs'').2 i]
    exact hK.inert s hs' i
  · intro s hs' i
    show (adj (P.n ()) * P.r s * P.n ()) i i - _ ∈ _
    rw [(hflag s hs').2 i]
    have h1 := hK.char s hs' i
    have h2 := ps_chi 𝔞 hlab hs' i
    have h3 := Ideal.add_mem _ h1 h2
    convert h3 using 1
    ring
