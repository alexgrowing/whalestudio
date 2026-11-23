import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.MemK2HpIffCong

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

variable {D : D7}

abbrev gLam (X : HidaSetting D) (p : TypX X) :
    Submodule (p.1.adicCompletionIntegers X.B.I.F) (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :=
  Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
    latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

theorem g_mem_p (X : HidaSetting D) (p : TypX X) : ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  have h0 : D.host.g 0 ≠ 0 := (D.host.g_prime 0).ne_zero
  have h1 : D.host.g 1 ≠ 0 := (D.host.g_prime 1).ne_zero
  have hp := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) h0 h1 p.1).1 p.2
  rw [X.g_eq, Nat.cast_mul]
  rcases hp with h | h
  · exact Ideal.mul_mem_right _ _ h
  · exact Ideal.mul_mem_left _ _ h

theorem coprime_not_mem (X : HidaSetting D) (p : TypX X) (c : ℕ) (hc : Nat.Coprime c X.B.g) :
    ((c : ℕ) : 𝓞 X.B.I.F) ∉ p.1.asIdeal := by
  intro h
  have hc' : IsCoprime ((c : ℕ) : ℤ) ((X.B.g : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨s, t, hst⟩ := hc'.map (Int.castRingHom (𝓞 X.B.I.F))
  simp only [eq_intCast, Int.cast_natCast] at hst
  apply p.1.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ (g_mem_p X p))

theorem loc_of_InAt (X : HidaSetting D) (p : TypX X) (w : VA X.B.I) (h : InAt X.B.I X.B.g X.B.g w) :
    PI.FinKW.vecV X.B.I p.1 w ∈ gLam X p := by
  obtain ⟨c, hc, hcw⟩ := h
  have h1 : InMod X.B.I X.B.g ∅ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w) := Submodule.mem_sup_right hcw
  have h2 := MassDataIdxSteps.imA_inMod_loc X p X.B.g ∅ _ h1
  rw [Set.image_empty] at h2
  have h3 : PI.FinKW.vecV X.B.I p.1 ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w) ∈ gLam X p := by
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 h2
    have ha0 : a = 0 := by
      have hs : {w : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E |
          ∃ t ∈ MassDataIdxSteps.OEp X p, ∃ s ∈ (∅ : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)),
            w = t • s} = ∅ := by
        ext w; simp
      rw [hs, Submodule.span_empty, Submodule.mem_bot] at ha
      exact ha
    rw [← e, ha0, zero_add]
    exact hb
  rw [MassDataIdxSteps.imA_vecV_smul, map_natCast, Nat.cast_smul_eq_nsmul,
    ← Nat.cast_smul_eq_nsmul (p.1.adicCompletionIntegers X.B.I.F)] at h3
  obtain ⟨u0, hu0⟩ := isUnit_natCast_of_not_mem p.1 c (coprime_not_mem X p c hc)
  have h4 := Submodule.smul_mem (gLam X p) ((u0⁻¹ : (p.1.adicCompletionIntegers X.B.I.F)ˣ) :
    p.1.adicCompletionIntegers X.B.I.F) h3
  rw [← hu0, smul_smul, Units.inv_mul, one_smul] at h4
  exact h4

theorem kloc_gLam (X : HidaSetting D) (p : TypX X)
    (M : GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (hM : M ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (v : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) (hv : v ∈ gLam X p) :
    (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ v ∈ gLam X p := by
  refine Submodule.smul_induction_on (p := fun v =>
    (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ v ∈ gLam X p) hv ?_ ?_
  · intro r hr l hl
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem_smul hr ((hM l).1 hl)
  · intro a b ha hb
    rw [Matrix.mulVec_add]
    exact add_mem ha hb

theorem kill_of_fix (X : HidaSetting D) (p : TypX X)
    (M : GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (hM : M ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (s t : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)
    (ht : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) _) *ᵥ t = t) (hst : s - t ∈ gLam X p) :
    ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ s ∈ gLam X p := by
  have e : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ s =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) _) *ᵥ (s - t) - (s - t) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, ht]
    abel
  rw [e]
  exact sub_mem (kloc_gLam X p M hM _ hst) hst

theorem vecV_fmat (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) (y : X.B.I.Gf) (w : VA X.B.I) :
    PI.FinKW.vecV X.B.I p.1 (X.B.I.fmat y *ᵥ w) =
      ((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb y)) :
        GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) _) *ᵥ
        PI.FinKW.vecV X.B.I p.1 w := by
  have h := MassDataIdxSteps.imA_vecV_mulVec X hb p y w
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, MassDataIdxSteps.imA_vecV_sub, Matrix.sub_mulVec, Matrix.one_mulVec] at h
  have h2 := congrArg (· + PI.FinKW.vecV X.B.I p.1 w) h
  simp only [sub_add_cancel] at h2
  exact h2

theorem vecV_incl (X : HidaSetting D) (p : TypX X) (y : Fin X.B.I.n → X.B.I.E) :
    PI.FinKW.vecV X.B.I p.1 (Formalism.L2.SG.HidaSetting.incl X.B.I y) = ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y := by
  funext i
  simp [PI.FinKW.vecV, PI.FinKW.psiV, Formalism.L2.SG.HidaSetting.incl, ratV, inclR, Formalism.UG.inclE]

theorem cong_head (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) (x : KvH X u p.1) :
    (∀ a : Fin D.R.rS, MassDataIdxSteps.InModP X p X.B.g
      ((fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) '' {b | b.1 < a.1})
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J ((xuP X hb u p)⁻¹ *
          ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) *
          xuP X hb u p) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 (X.e0 a))) ∧
    MassDataIdxSteps.InModP X p X.B.g (Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b))
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J ((xuP X hb u p)⁻¹ *
          ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) *
          xuP X hb u p) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 X.z0) := by
  set A := HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) with hA_def
  set Y := HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J
    ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)
    with hY_def
  have hM : HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J ((xuP X hb u p)⁻¹ *
      ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) *
      xuP X hb u p) = A⁻¹ * Y * A := rfl
  have hAK : A ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := unipotent_mem_localStabilizer X hb u p
  have hYK : Y ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := x.2
  have hMK : A⁻¹ * Y * A ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    mul_mem (mul_mem (inv_mem hAK) hYK) hAK
  have hxH := (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)).2
  have hfix : ∀ b, (Y : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ
      ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (tupH (frameOf X u) b) =
      ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (tupH (frameOf X u) b) := by
    intro b
    have := (mem_stabT (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u)) _).1 hxH b
    exact this
  have hinv : ∀ v, (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ v = v →
      ((A⁻¹ : GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ v = v := by
    intro v hv
    calc ((A⁻¹ : GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ v
        = ((A⁻¹ : GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ
            ((A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨fun a => ?_, ?_⟩
  ·
    set t := ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.eX a)) with ht_def
    have hAt : (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ t = t := by
      have h1 := vecV_fmat X hb p (X.xu u) (Formalism.L2.SG.HidaSetting.incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX a)))
      rw [(X.xu_fix u a).1, vecV_incl] at h1
      exact h1.symm
    have hYt : (Y : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ t = t := by
      have := hfix (Fin.castAdd D.R.rS (Fin.castSucc a))
      rw [tupH, Fin.append_left, F0, Fin.snoc_castSucc] at this
      exact this
    have hMt : ((A⁻¹ * Y * A : GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ t = t := by
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAt, hYt, hinv t hAt]
    have hst : PI.FinKW.vecV X.B.I p.1 (X.e0 a) - t ∈ gLam X p := by
      rw [ht_def, ← vecV_incl, ← MassDataIdxSteps.imA_vecV_sub]
      exact loc_of_InAt X p _ (X.basisApprox a).1
    rw [hM]
    exact Submodule.mem_sup_right (kill_of_fix X p _ hMK _ t hMt hst)
  ·
    set t := PI.FinKW.vecV X.B.I p.1 (X.B.I.fmat (X.xu u)⁻¹ *ᵥ
      Formalism.L2.SG.HidaSetting.incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u))) with ht_def
    have hz : (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ t =
        ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.zu u)) := by
      rw [ht_def, vecV_fmat X hb p, vecV_incl, Matrix.mulVec_mulVec]
      have e1 : PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb (X.xu u)⁻¹) = (xuP X hb u p)⁻¹ := by
        rw [finHA_inv, map_inv]
      have e2 : (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *
          ((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb (X.xu u)⁻¹)) :
            GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) = 1 := by
        rw [e1]
        show ((A * A⁻¹ : GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) = 1
        rw [mul_inv_cancel, Units.val_one]
      rw [e2, Matrix.one_mulVec]
    have hYz : (Y : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ
        ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.zu u)) =
        ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.zu u)) := by
      have := hfix (Fin.castAdd D.R.rS (Fin.last D.R.rS))
      rw [tupH, Fin.append_left, F0, Fin.snoc_last] at this
      exact this
    have hMt : ((A⁻¹ * Y * A : GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) *ᵥ t = t := by
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz, hYz, ← hz,
        Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hst : PI.FinKW.vecV X.B.I p.1 X.z0 - t ∈ gLam X p := by
      have h0 := loc_of_InAt X p _ (X.xu_z u)
      rw [MassDataIdxSteps.imA_vecV_sub] at h0
      have h1 := neg_mem h0
      rw [neg_sub] at h1
      exact h1
    rw [hM]
    exact Submodule.mem_sup_right (kill_of_fix X p _ hMK _ t hMt hst)

theorem mem_K2Hp_iff_beta (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (p : TypX X) (x : KvH X u p.1) :
    x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔
      ∀ i : Fin D.R.k, MassDataIdxSteps.InModP X p X.B.g ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
        (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j | j.1 < i.1})
        (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J ((xuP X hb u p)⁻¹ *
          ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) *
          xuP X hb u p) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
          PI.FinKW.vecV X.B.I p.1 (X.bw i)) := by
  rw [mem_K2Hp_iff_cong X hb hK hL u p x]
  obtain ⟨h1, h2⟩ := cong_head X hb u p x
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨h1, h2, h⟩

end PIW.MassDataColumns
