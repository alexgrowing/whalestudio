import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusHeights.ContinuousHom

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Orb

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BStep

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def StepModH : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ (t : kˣ) (p : Sp k n) (g : GL (Fin n) k),
    g ∈ Gz Z → act g p = PositivityTheory.RgUd.TP.Nil.hom t p → p.2 ≠ 0 → ∀ (K : Subgroup (GL (Fin n) k)), K ≤ GzS Z → IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) →
    IsCompact (K : Set (GL (Fin n) k)) → ∀ L : Subgroup (GL (Fin n) k), IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) →
    L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom → L.Normal' K → L.Normal' (K.map (MulAut.conj g).toMonoidHom) →
    ∀ (C U : Set (Sp k n)), IsClosed C → IsOpen U → U ∩ C = orb Z p →
    (∀ h ∈ Gz Z, ∀ q ∈ C, act h q ∈ C) → (∀ q ∈ C, PositivityTheory.RgUd.TP.Nil.hom t q ∈ C) → ∀ ξ, PositivityTheory.RgUd.TP.Nil.InvU Z ξ →
      PositivityTheory.RgUd.TP.Nil.SuppU ξ C →
      PositivityTheory.RgUd.TP.Nil.SuppU (PositivityTheory.RgUd.TP.Nil.pullH t ξ - ((modul (stab Z p) K L g : ℝ) : ℂ) • ξ) (C \ U)

theorem stepH : StepModH k := by
  intro n Z _hZ t p g hg hgp hp2 K hKG hKo hKc L hLo hLK hLn hLn' C U hC hU hUC hCinv hCsig ξ hξ hξC
  classical
  have hξC : PositivityTheory.RgUd.T.Nil.Orb.SuppU ξ C := hξC
  have : T2Space (SpT k n) := t2Sp
  have : LocallyCompactSpace (SpT k n) := lcSp
  have : TotallyDisconnectedSpace (SpT k n) := tdSp
  have : ContinuousSMul (GL (Fin n) k) (SpT k n) := contSMul
  have : LocallyCompactSpace (GzS Z) := lcH Z
  have : TotallyDisconnectedSpace (GzS Z) := tdH Z
  have : SigmaCompactSpace (GzS Z) := scH Z
  have : ContinuousSMul (GzS Z) (SpT k n) := contSMulH Z

  let gH : GzS Z := ⟨g, hg⟩
  set K' : Subgroup (GL (Fin n) k) := K.map (MulAut.conj g).toMonoidHom with hK'def
  have hK'G : K' ≤ GzS Z := by
    rintro _ ⟨x, hx, rfl⟩
    exact (GzS Z).mul_mem ((GzS Z).mul_mem hg (hKG hx)) ((GzS Z).inv_mem hg)
  set KH := K.subgroupOf (GzS Z) with hKHdef
  set K'H := K'.subgroupOf (GzS Z) with hK'Hdef
  set LH := L.subgroupOf (GzS Z) with hLHdef
  have hKHc : IsCompact (KH : Set (GzS Z)) := isCompact_subgroupOf Z hKG hKc
  have hKHo : IsOpen (KH : Set (GzS Z)) := hKo
  have hLHo : IsOpen (LH : Set (GzS Z)) := hLo
  have hK'H : K'H = KH.map (MulAut.conj gH).toMonoidHom := by
    ext x
    simp only [hK'Hdef, hKHdef, Subgroup.mem_subgroupOf, Subgroup.mem_map, hK'def]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨y, hKG hy⟩, hy, Subtype.ext ?_⟩
      simpa [MulAut.conj_apply] using hyx
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp [MulAut.conj_apply, gH]⟩
  have hK'Hco := isCompact_isOpen_map_conj hKHc hKHo gH
  rw [← hK'H] at hK'Hco
  have hLKH : LH ≤ KH := fun x hx => (hLK hx).1
  have hLK'H : LH ≤ K'H := fun x hx => (hLK hx).2
  have hLHc : IsCompact (LH : Set (GzS Z)) :=
    hKHc.of_isClosed_subset (LH.isClosed_of_isOpen hLHo) hLKH
  have hnK : ∀ j ∈ KH, ∀ a ∈ LH, j * a * j⁻¹ ∈ LH := fun j hj a ha => hLn _ hj _ ha
  have hnK' : ∀ j ∈ K'H, ∀ a ∈ LH, j * a * j⁻¹ ∈ LH := fun j hj a ha => hLn' _ hj _ ha

  let U₁ : Set (Sp k n) := {q | q.2 ≠ 0 ∧ ∃ h ∈ Gz Z, act h q ∈ U}
  have hU₁o : IsOpen U₁ := by
    have e : U₁ = UU ∩ ⋃ h : GzS Z, (fun q => act (h : GL (Fin n) k) q) ⁻¹' U := by
      ext q
      simp only [U₁, UU, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨h2, h, hh, hq⟩
        exact ⟨h2, ⟨h, hh⟩, hq⟩
      · rintro ⟨h2, h, hq⟩
        exact ⟨h2, h.1, h.2, hq⟩
    rw [e]
    refine isOpen_UU.inter (isOpen_iUnion fun h => hU.preimage ?_)
    exact (continuous_const_smul (h : GL (Fin n) k) : Continuous fun q : SpT k n => (h : GL (Fin n) k) • q)
  have hU₁UU : U₁ ⊆ UU := fun q hq => hq.1
  have hU₁inv : ∀ h : GzS Z, ∀ x : SpT k n, x ∈ (U₁ : Set (SpT k n)) → h • x ∈ (U₁ : Set (SpT k n)) := by
    rintro h x ⟨hx2, h', hh', hx⟩
    refine ⟨act_snd_ne (h : GL (Fin n) k) hx2, h' * (h : GL (Fin n) k)⁻¹,
      (GzS Z).mul_mem hh' ((GzS Z).inv_mem h.2), ?_⟩
    have e : act (h' * (h : GL (Fin n) k)⁻¹) (act (h : GL (Fin n) k) (x : Sp k n)) = act h' x := by
      rw [act_mul]
      exact congrArg (act h') (act_inv_act _ _)
    change act (h' * (h : GL (Fin n) k)⁻¹) (act (h : GL (Fin n) k) (x : Sp k n)) ∈ U
    rw [e]
    exact hx
  have hU₁oT : IsOpen (X := SpT k n) U₁ := hU₁o
  have hCT : IsClosed (X := SpT k n) C := hC
  have horb : orb Z p ⊆ U ∩ C := by rw [hUC]
  have hO₁ : U₁ ∩ C = orb Z p := by
    ext q
    constructor
    · rintro ⟨⟨-, h, hh, hqU⟩, hqC⟩
      have hm : act h q ∈ orb Z p := hUC ▸ ⟨hqU, hCinv h hh q hqC⟩
      obtain ⟨g', hg', e⟩ := hm
      refine ⟨h⁻¹ * g', (GzS Z).mul_mem ((GzS Z).inv_mem hh) hg', ?_⟩
      rw [act_mul, e, act_inv_act]
    · intro hq
      have hq' := horb hq
      obtain ⟨h, _, rfl⟩ := hq
      exact ⟨⟨act_snd_ne h hp2, 1, (GzS Z).one_mem, by rw [act_one]; exact hq'.1⟩, hq'.2⟩
  have hOorb : orbit (GzS Z) (toT p) = orb Z p := Set.ext fun q => mem_orbit_iff' Z (p := p) (q := q)
  have hO₁' : ((U₁ : Set (SpT k n)) ∩ C) = orbit (GzS Z) (toT p) := by rw [hOorb]; exact hO₁
  have hp0 : toT p ∈ orbit (GzS Z) (toT p) := mem_orbit_self (toT p)
  have hlift : ∀ B : Subgroup (GzS Z), IsCompact (B : Set (GzS Z)) → IsOpen (B : Set (GzS Z)) →
      ∃ f ∈ supportedIn U₁, ∀ x ∈ orb Z p, f x = (orbitPiece B (toT p)).indicator 1 (toT x) := by
    intro B hBc hBo
    obtain ⟨f, hf, hfO⟩ := exists_lift_orbit_piece (X := SpT k n) hU₁oT hCT hO₁' hBc hBo hp0
    exact ⟨f, hf, fun x hx => hfO (toT x) (hOorb ▸ hx)⟩
  obtain ⟨f₀, hf₀, hf₀O⟩ := hlift KH hKHc hKHo
  obtain ⟨f₁, hf₁, hf₁O⟩ := hlift K'H hK'Hco.1 hK'Hco.2
  obtain ⟨fL, hfL, hfLO⟩ := hlift LH hLHc hLHo
  have hPsub : ∀ B : Subgroup (GzS Z), ∀ x, toT x ∈ orbitPiece B (toT p) → x ∈ orb Z p := by
    intro B x hx
    exact (mem_orbit_iff' Z).1 (orbitPiece_subset_orbit hp0 hx)

  set m : ℂ := ((modul (stab Z p) K L g : ℝ) : ℂ) with hm
  set ψ := PositivityTheory.RgUd.TP.Nil.pullH t ξ - m • ξ with hψdef
  have hψ : ∀ f, ψ f = ξ (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t q)) - m * ξ f := fun f => rfl

  have hV : ∀ v ∈ supportedIn UU, (∀ q ∈ C, v q = 0) → ψ v = 0 := by
    intro v hv hvC
    rw [hψ, hξC v hv hvC, hξC _ (comp_hom_mem t hv) (fun q hq => hvC _ (hCsig q hq))]
    simp

  have hR : relSpan (X := SpT k n) (1 : GzS Z →* ℂ) U₁ ≤ LinearMap.ker ψ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, f, hf, rfl⟩
    have hfUU : f ∈ supportedIn UU := supportedIn_mono hU₁UU hf
    simp only [MonoidHom.one_apply, one_smul]
    change ψ (transl (X := SpT k n) h f - f) = 0
    have e1 : ξ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) = ξ f :=
      hξ _ (h⁻¹).2 f hfUU
    have e2 : ξ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) (PositivityTheory.RgUd.TP.Nil.hom t q))) = ξ (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t q)) := by
      have := hξ _ (h⁻¹).2 (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t q)) (comp_hom_mem t hfUU)
      rw [← this]
      congr 1
      funext q
      rw [hom_act t]
    have key : ψ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) = ψ f := by
      rw [hψ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)), hψ f, e1]
      exact congrArg (· - m * ξ f) e2
    have hs : ψ (fun q : Sp k n => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q) - f q) =
        ψ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) - ψ f :=
      ψ.map_sub (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) f
    change ψ (fun q : Sp k n => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q) - f q) = 0
    rw [hs, key, sub_self]

  have hsig_piece : ∀ q : Sp k n, toT (PositivityTheory.RgUd.TP.Nil.hom t q) ∈ orbitPiece KH (toT p) ↔
      toT (act g q) ∈ orbitPiece K'H (toT p) := by
    intro q
    constructor
    · rintro ⟨κ, hκ, e⟩
      change act (κ : GL (Fin n) k) p = PositivityTheory.RgUd.TP.Nil.hom t q at e
      have hq : q = act ((κ : GL (Fin n) k) * g⁻¹) p := by
        have h1 : PositivityTheory.RgUd.TP.Nil.hom t (act ((κ : GL (Fin n) k) * g⁻¹) p) = PositivityTheory.RgUd.TP.Nil.hom t q := by
          rw [hom_act t, ← hgp, ← act_mul,
            inv_mul_cancel_right, e]
        have := congrArg (PositivityTheory.RgUd.TP.Nil.hom t⁻¹) h1
        rw [hom_inv_hom t, hom_inv_hom t] at this
        exact this.symm
      refine ⟨⟨g * (κ : GL (Fin n) k) * g⁻¹, hK'G ⟨κ, hκ, rfl⟩⟩, ⟨κ, hκ, rfl⟩, ?_⟩
      change act (g * (κ : GL (Fin n) k) * g⁻¹) p = act g q
      rw [hq, ← act_mul, mul_assoc]
    · rintro ⟨κ', ⟨κ, hκ, hκe⟩, e⟩
      change act (κ' : GL (Fin n) k) p = act g q at e
      have hκ' : (κ' : GL (Fin n) k) = g * κ * g⁻¹ := by simpa [MulAut.conj_apply] using hκe.symm
      have hq : q = act (κ * g⁻¹) p := by
        have := congrArg (act g⁻¹) e
        rw [act_inv_act, ← act_mul, hκ'] at this
        rw [← this]
        congr 1
        group
      refine ⟨⟨κ, hKG hκ⟩, hκ, ?_⟩
      change act κ p = PositivityTheory.RgUd.TP.Nil.hom t q
      rw [hq, hom_act t, ← hgp, ← act_mul,
        inv_mul_cancel_right]
  have hf₀UU : f₀ ∈ supportedIn UU := supportedIn_mono hU₁UU hf₀
  have hf₁UU : f₁ ∈ supportedIn UU := supportedIn_mono hU₁UU hf₁
  have hX1 : ξ (fun q => f₀ (PositivityTheory.RgUd.TP.Nil.hom t q)) = ξ f₁ := by
    rw [← hξ g hg f₁ hf₁UU]
    refine xi_eq hξC (comp_hom_mem t hf₀UU) (comp_act_memUU g hf₁UU) fun q hq => ?_
    rw [lift_on_C' hO₁ (hPsub KH) hf₀ hf₀O _ (hCsig q hq),
      lift_on_C' hO₁ (hPsub K'H) hf₁ hf₁O _ (hCinv g hg q hq)]
    by_cases h : toT (PositivityTheory.RgUd.TP.Nil.hom t q) ∈ orbitPiece KH (toT p)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hsig_piece q).1 h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hsig_piece q).2 h'))]

  have hc0 := piece_countU Z hξ hC hU₁o hU₁UU hCinv hO₁ hξC hKHc hLHo hLKH hnK hf₀ hfL hf₀O hfLO
  have hc1 := piece_countU Z hξ hC hU₁o hU₁UU hCinv hO₁ hξC hK'Hco.1 hLHo hLK'H hnK' hf₁ hfL hf₁O hfLO
  have ha0 : LH.relIndex KH ≠ 0 := relIndex_ne_zero hKHc hLHo
  have ha1 : LH.relIndex K'H ≠ 0 := relIndex_ne_zero hK'Hco.1 hLHo
  have hb0 := right_ne_zero_of_mul ((count KH LH hLKH hnK (toT p)).symm ▸ ha0)
  have hb1 := right_ne_zero_of_mul ((count K'H LH hLK'H hnK' (toT p)).symm ▸ ha1)
  obtain ⟨r0, s0⟩ := relIndex_H Z p (L := L) hKG
  obtain ⟨r1, s1⟩ := relIndex_H Z p (L := L) hK'G
  have hmodul : modul (stab Z p) K L g =
      ((LH.relIndex K'H : ℝ) / ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (K'H ⊓ stabilizer (GzS Z) (toT p)) : ℝ)) /
      ((LH.relIndex KH : ℝ) / ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (KH ⊓ stabilizer (GzS Z) (toT p)) : ℝ)) := by
    rw [modul, ← hK'def, r0, s0, r1, s1]
  have hP : ψ f₀ = 0 := by
    rw [hψ, hX1, hm, hmodul]
    have ha0' : (LH.relIndex KH : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha0
    have ha1' : (LH.relIndex K'H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha1
    have hb0' : ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (KH ⊓ stabilizer (GzS Z) (toT p)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 hb0
    have hb1' : ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (K'H ⊓ stabilizer (GzS Z) (toT p)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 hb1
    have e0 := eq_div_of_mul_eq hb0' hc0
    have e1 := eq_div_of_mul_eq hb1' hc1
    rw [e0, e1]
    push_cast
    field_simp
    ring

  have hWU : relSpan (X := SpT k n) (1 : GzS Z →* ℂ) U₁ ⊔ Submodule.span ℂ {f₀} ≤ supportedIn (X := SpT k n) U₁ :=
    sup_le (relSpan_le_supportedIn _ hU₁inv) ((Submodule.span_singleton_le_iff_mem _ _).2 hf₀)
  have hle := supportedIn_le_of_base (X := SpT k n) hU₁oT hCT hO₁' hU₁inv (1 : GzS Z →* ℂ) hWU le_sup_left KH hKHc hKHo
    (fun _ _ => rfl) f₀ (fun x hx => hf₀O x (hOorb ▸ hx))
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self f₀)))
  have hker : supportedIn (X := SpT k n) U₁ ≤ LinearMap.ker ψ :=
    hle.trans (sup_le (sup_le hR ((Submodule.span_singleton_le_iff_mem _ _).2 hP))
      fun v hv => hV v (supportedIn_mono hU₁UU hv.1) hv.2)

  intro f hf hfCU
  have hKc' : IsCompact (X := SpT k n) (C ∩ Function.support f) := (isCompact_support hf.1).inter_left hC
  have hsub : C ∩ Function.support f ⊆ U₁ := by
    rintro q ⟨hqC, hqf⟩
    have hqU : q ∈ U := by
      by_contra h
      exact hqf (hfCU q ⟨hqC, h⟩)
    have hq : q ∈ orb Z p := hUC ▸ ⟨hqU, hqC⟩
    rw [← hO₁] at hq
    exact hq.1
  obtain ⟨B, hBc, hBo, hKB, hBU⟩ := exists_isCompact_isOpen_between (X := SpT k n) hKc' hU₁oT hsub
  set f₂ : Sp k n → ℂ := fun x => B.indicator 1 (toT x) * f x with hf₂def
  have hf₂ : f₂ ∈ supportedIn (X := SpT k n) U₁ := by
    refine ⟨(indicator_mul_mem (X := SpT k n) ⟨hBc.isClosed, hBo⟩ hf).1, fun x hx => ?_⟩
    have hxB : toT x ∈ B := by
      by_contra h
      have h0 : B.indicator 1 (toT x) = (0 : ℂ) := Set.indicator_of_notMem h _
      exact hx (show B.indicator 1 (toT x) * f x = 0 by rw [h0, zero_mul])
    exact hBU hxB
  have e : f = f₂ + (f - f₂) := by abel
  change ψ f = 0
  rw [e, map_add, hker hf₂, zero_add]
  refine hV _ (Submodule.sub_mem _ hf (supportedIn_mono hU₁UU hf₂)) fun q hq => ?_
  by_cases hfq : f q = 0
  · simp [f₂, hfq]
  · have hqB : toT q ∈ B := hKB ⟨hq, hfq⟩
    simp [f₂, Set.indicator_of_mem hqB]

end PositivityTheory.RgUd.TP.Nil.Orb
