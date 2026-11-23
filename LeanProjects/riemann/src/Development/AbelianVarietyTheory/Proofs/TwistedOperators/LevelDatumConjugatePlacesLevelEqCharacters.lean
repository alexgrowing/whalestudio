import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDatComb

open GlobalTheory.LiftLevel GlobalTheory.LiftDat

variable {D : D7}

theorem conjI_eq_comap (P : Ideal (𝓞 D.host.E)) : conjI P = P.comap GlobalTheory.SW.Lev.bar := by
  ext a; rw [GlobalTheory.SW.Lev.mem_conjI, Ideal.mem_comap]

theorem bar_surj : Function.Surjective (GlobalTheory.SW.Lev.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
  fun a => ⟨GlobalTheory.SW.Lev.bar a, GlobalTheory.SW.Lev.bar_bar a⟩

theorem conjI_isMax (PP : Formalism.L2.DIV.Pl D.host.E) : (conjI PP.asIdeal).IsMaximal := by
  rw [conjI_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ bar_surj

theorem conjI_inj {P P' : Ideal (𝓞 D.host.E)} (h : conjI P = conjI P') : P = P' := by
  ext a
  have := SetLike.ext_iff.1 h (GlobalTheory.SW.Lev.bar a)
  rwa [GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.bar_bar] at this

theorem mem_liftI {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {x : 𝓞 D.host.E} :
    x ∈ liftI Pg Q ↔ ∀ PP ∈ Pg ∪ Q, GlobalTheory.SW.Lev.bar x ∈ PP.asIdeal := by
  constructor
  · intro hx PP hPP
    exact GlobalTheory.SW.Lev.mem_conjI.1 (liftI_le hPP hx)
  · intro h
    unfold liftI
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp only [Submodule.mem_iInf]
      intro PP hPP
      exact GlobalTheory.SW.Lev.mem_conjI.2 (h PP hPP)
    · intro PP _ PP' _ hne
      have hne' : conjI PP.asIdeal ≠ conjI PP'.asIdeal := fun e =>
        hne (HeightOneSpectrum.ext (conjI_inj e))
      exact (Ideal.isCoprime_iff_sup_eq).2 ((conjI_isMax PP).coprime_of_ne (conjI_isMax PP') hne')

theorem isUnit_mk_liftI {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {x : 𝓞 D.host.E}
    (h : ∀ PP ∈ Pg ∪ Q, GlobalTheory.SW.Lev.bar x ∉ PP.asIdeal) : IsUnit (Ideal.Quotient.mk (liftI Pg Q) x) := by
  have hc : IsCoprime (Ideal.span {x}) (liftI Pg Q) := by
    unfold liftI
    refine IsCoprime.prod_right fun PP hPP => ?_
    have hx : x ∉ conjI PP.asIdeal := fun hm => h PP hPP (GlobalTheory.SW.Lev.mem_conjI.1 hm)
    obtain ⟨y, i, hi, e⟩ := (conjI_isMax PP).exists_inv hx
    exact Ideal.isCoprime_iff_exists.2 ⟨y * x, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x), i, hi, e⟩
  obtain ⟨i, hi, j, hj, e⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ a, ?_⟩
  have : Ideal.Quotient.mk (liftI Pg Q) j = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hj
  rw [← map_mul, mul_comm, eq_sub_of_add_eq e, map_sub, this, sub_zero, map_one]

section CongLemmas
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)

theorem cong_of_sub_mem {𝔪 : Ideal (𝓞 E)} {u v : Fin r → E} (h : u - v ∈ 𝔪 • X.Λ) : GlobalTheory.SW.Cong X 𝔪 u v :=
  ⟨1, by rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq, top_sup_eq], by rwa [one_smul]⟩

theorem cong_congr_left {𝔪 : Ideal (𝓞 E)} {y u v : Fin r → E} (hy : y - u ∈ 𝔪 • X.Λ)
    (h : GlobalTheory.SW.Cong X 𝔪 y v) : GlobalTheory.SW.Cong X 𝔪 u v := by
  obtain ⟨s, hs, hm⟩ := h
  refine ⟨s, hs, ?_⟩
  have : s • (u - v) = s • (y - v) - s • (y - u) := by
    rw [← smul_sub]; congr 1; abel
  rw [this]
  exact sub_mem hm (Submodule.smul_mem _ s hy)

theorem sum_mem_of_coeff {𝔪 : Ideal (𝓞 E)} {m : ℕ} (β : Fin m → Fin r → E) (hβ : ∀ i, β i ∈ X.Λ)
    (d : Fin m → 𝓞 E) (hd : ∀ j, d j ∈ 𝔪) : ∑ j, d j • β j ∈ 𝔪 • X.Λ :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hd j) (hβ j)

end CongLemmas

section Mat
open GlobalTheory.LiftLevel GlobalTheory.LiftDat
variable {D : D7}

theorem mk_conjI_eq_iff (P : Ideal (𝓞 D.host.E)) (x y : 𝓞 D.host.E) :
    Ideal.Quotient.mk (conjI P) x = Ideal.Quotient.mk (conjI P) y ↔
      Ideal.Quotient.mk P (GlobalTheory.SW.Lev.bar x) = Ideal.Quotient.mk P (GlobalTheory.SW.Lev.bar y) := by
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq, GlobalTheory.SW.Lev.mem_conjI, map_sub]

theorem mapMat_eq_one_iff {R' : Type*} [CommRing R'] {r : ℕ} (f : 𝓞 D.host.E →+* R')
    (A : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) :
    A.map f = 1 ↔ ∀ a b, f (A a b) = f ((1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) a b) := by
  rw [← Matrix.map_one f (map_zero f) (map_one f), ← Matrix.ext_iff]
  simp only [Matrix.map_apply]

theorem jgrp_iff {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ} (κ : GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q))
    (ct : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) (hκ : κ.val = ctᵀ.map (Ideal.Quotient.mk _)) :
    κ ∈ Jgrp Pg Q r ↔ ∀ PP ∈ Pg, ct.map ((Ideal.Quotient.mk PP.asIdeal).comp GlobalTheory.SW.Lev.bar) = 1 := by
  rw [mem_Jgrp]
  refine forall₂_congr fun PP hPP => ?_
  rw [Units.ext_iff]
  have e1 : ((Matrix.GeneralLinearGroup.map (toConj Pg Q PP (Finset.mem_union_left _ hPP)) κ :
      GL (Fin r) _) : Matrix (Fin r) (Fin r) _) = ct.transpose.map (Ideal.Quotient.mk (conjI PP.asIdeal)) := by
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply, hκ]
    rfl
  rw [e1, Units.val_one, Matrix.transpose_map, Matrix.transpose_eq_one, mapMat_eq_one_iff, mapMat_eq_one_iff]
  exact forall₂_congr fun a b => mk_conjI_eq_iff _ _ _

theorem conjRes_det {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ Pg ∪ Q) {r : ℕ}
    (ct : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) :
    conjRes Pg Q PP h (ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q))).det =
      (ct.map ((Ideal.Quotient.mk PP.asIdeal).comp GlobalTheory.SW.Lev.bar)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_map, Matrix.transpose_map, Matrix.det_transpose]
  rfl

end Mat

end GlobalTheory.LiftDatComb

namespace GlobalTheory.LiftDat

open GlobalTheory.LiftDatComb GlobalTheory.LiftLevel

theorem dat_mkLevel_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤) (h2 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥) (h3 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q))) (h4 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2})) (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ) (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) (Lv0 : GlobalTheory.SW.Level C.X), (∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 → ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q) → ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (c : Fin S.rank → Fin T.rank → 𝓞 D.host.E), (∀ i, y i - ∑ j, c i j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) → ∀ Y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP), (∀ PP ∈ Pg ∪ Q, ∀ i j, Y PP i j = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c i j))) → (GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0).dat hn y = omegaK Pg Y * omegaQ Q T.rank ξ (-1) Y := by
  intro D S T C hn Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0 hind y c hyc Y hY
  set ct : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E) := fun a b => c (Fin.castLE hn a) b with hct
  have hTop : ∀ PP ∈ Pg ∪ Q, topL T.rank (Y PP) = ct.map ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar) := by
    intro PP hPP
    ext a b
    rw [topL, dif_pos ⟨lt_of_lt_of_le a.2 hn, b.2⟩, hY PP hPP]
    rfl
  have hcong0 : ∀ i, GlobalTheory.SW.Cong C.X (liftI Pg Q) (y i) 0 ↔ ∀ j, c i j ∈ liftI Pg Q := by
    intro i
    constructor
    · intro hc
      obtain ⟨s, hs, hm⟩ := cong_congr_left C.X (hyc i) hc
      exact hind (c i) ⟨s, hs, hm⟩
    · intro hc
      refine cong_of_sub_mem C.X ?_
      rw [sub_zero, ← sub_add_cancel (y i) (∑ j, c i j • β j)]
      exact add_mem (hyc i) (sum_mem_of_coeff C.X β hβ _ hc)
  have hrow : ∀ PP ∈ Pg ∪ Q, ∀ i j, (Y PP i j = 0 ↔ Lev.bar (c i j) ∈ PP.asIdeal) := by
    intro PP hPP i j
    rw [hY PP hPP, Ideal.Quotient.eq_zero_iff_mem]
  have hdetU : ∀ PP ∈ Pg ∪ Q, IsUnit (topL T.rank (Y PP)).det → Lev.bar ct.det ∉ PP.asIdeal := by
    intro PP hPP hu hm
    have e : (ct.map ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar)).det =
        ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar) ct.det := (RingHom.map_det _ _).symm
    rw [hTop PP hPP, e, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hm] at hu
    exact not_isUnit_zero hu
  set L := mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0 with hL
  unfold Level.dat
  by_cases h : (∃ k : L.J, L.Red (fun i => y (Fin.castLE hn i)) k) ∧
      ∀ k : Fin S.rank, T.rank ≤ (k : ℕ) → GlobalTheory.SW.Cong C.X L.𝔪 (y k) 0
  · rw [dif_pos h]
    obtain ⟨k', hk'm, hk'c⟩ := h.1.choose_spec
    set κ := h.1.choose with hκdef
    have hκval : (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)).val =
        ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q)) := by
      rw [← hk'm]
      ext a b
      simp only [Matrix.map_apply, Matrix.transpose_apply]
      refine Ideal.Quotient.eq.2 ?_
      obtain ⟨s, hs, hm⟩ := cong_congr_left C.X (hyc (Fin.castLE hn b)) (hk'c b)
      have := hind (fun j => c (Fin.castLE hn b) j - k' j b)
        ⟨s, hs, by
          convert hm using 2
          simp only [sub_zero, sub_smul, Finset.sum_sub_distrib]
          rfl⟩ a
      rw [← neg_sub]
      exact neg_mem this
    have hJ := (jgrp_iff (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)) ct hκval).1 κ.2
    have hlowc : ∀ i : Fin S.rank, T.rank ≤ (i : ℕ) → ∀ j, c i j ∈ liftI Pg Q :=
      fun i hi => (hcong0 i).1 (h.2 i hi)
    have hLow : ∀ PP ∈ Pg ∪ Q, LowZero T.rank (Y PP) :=
      fun PP hPP i j hi _ => (hrow PP hPP i j).2 (mem_liftI.1 (hlowc i hi j) PP hPP)
    have hdetQ : ∀ PP (hPP : PP ∈ Pg ∪ Q), conjRes Pg Q PP hPP
        (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)).val.det = (topL T.rank (Y PP)).det := by
      intro PP hPP
      rw [hκval]
      exact (conjRes_det hPP ct).trans (congrArg Matrix.det (hTop PP hPP).symm)
    have hQc : ∀ PP ∈ Q, LowZero T.rank (Y PP) ∧ IsUnit (topL T.rank (Y PP)).det := fun PP hPP =>
      ⟨hLow PP (Finset.mem_union_right _ hPP), by
        rw [← hdetQ PP (Finset.mem_union_right _ hPP), ← Matrix.GeneralLinearGroup.val_det_apply]
        exact (Units.isUnit _).map _⟩
    have hK : omegaK Pg Y = 1 := by
      unfold omegaK
      rw [if_pos]
      intro PP hPP
      exact ⟨hLow PP (Finset.mem_union_left _ hPP), by rw [hTop PP (Finset.mem_union_left _ hPP)]; exact hJ PP hPP⟩
    rw [hK, one_mul]
    unfold omegaQ
    rw [dif_pos hQc]
    show ((lamHom Pg Q T.rank ξ (⟨κ.1, κ.2⟩ : Jgrp Pg Q T.rank) : ℂˣ) : ℂ) = _
    rw [lamHom_apply, Units.val_inv_eq_inv_val, Units.coe_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : Units.map (conjRes Pg Q PP.1 (Finset.mem_union_right _ PP.2)).toMonoidHom
        (Matrix.GeneralLinearGroup.det (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q))) =
        (hQc PP.1 PP.2).2.unit := by
      ext
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, IsUnit.unit_spec,
        Matrix.GeneralLinearGroup.val_det_apply]
      exact hdetQ _ _
    rw [e, _root_.zpow_neg_one]
  · rw [dif_neg h]
    symm
    by_contra hne
    have hK : omegaK Pg Y ≠ 0 := left_ne_zero_of_mul hne
    have hQ : omegaQ Q T.rank ξ (-1) Y ≠ 0 := right_ne_zero_of_mul hne
    have hKc : ∀ PP ∈ Pg, LowZero T.rank (Y PP) ∧ topL T.rank (Y PP) = 1 := by
      by_contra hc
      exact hK (by unfold omegaK; rw [if_neg hc])
    have hQc : ∀ PP ∈ Q, LowZero T.rank (Y PP) ∧ IsUnit (topL T.rank (Y PP)).det := by
      by_contra hc
      exact hQ (by unfold omegaQ; rw [dif_neg hc])
    apply h
    have hLow : ∀ PP ∈ Pg ∪ Q, LowZero T.rank (Y PP) := by
      intro PP hPP
      rcases Finset.mem_union.1 hPP with hP | hP
      exacts [(hKc PP hP).1, (hQc PP hP).1]
    have hlowc : ∀ i : Fin S.rank, T.rank ≤ (i : ℕ) → ∀ j, c i j ∈ liftI Pg Q := fun i hi j =>
      mem_liftI.2 fun PP hPP => (hrow PP hPP i j).1 (hLow PP hPP i j hi j.2)
    have hdet : IsUnit (ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q))).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
      refine isUnit_mk_liftI fun PP hPP => hdetU PP hPP ?_
      rcases Finset.mem_union.1 hPP with hP | hP
      · rw [(hKc PP hP).2, Matrix.det_one]
        exact isUnit_one
      · exact (hQc PP hP).2
    set κ : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q) :=
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit with hκ
    have hκval : κ.val = ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q)) := IsUnit.unit_spec _
    have hκJ : κ ∈ Jgrp Pg Q T.rank := (jgrp_iff κ ct hκval).2 fun PP hPP => by
      rw [← hTop PP (Finset.mem_union_left _ hPP)]
      exact (hKc PP hPP).2
    exact ⟨⟨⟨κ, hκJ⟩, ctᵀ, hκval.symm, fun i => cong_of_sub_mem C.X (hyc (Fin.castLE hn i))⟩,
      fun k hk => (hcong0 k).2 (hlowc k hk)⟩

end GlobalTheory.LiftDat
