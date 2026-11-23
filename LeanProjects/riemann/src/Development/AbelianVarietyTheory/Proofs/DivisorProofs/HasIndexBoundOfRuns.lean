import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NusOfEqRamMulNuStarAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IndexBoundAtLargerField

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.BigOn

theorem isLattice_of_spanK {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {C : Type}
    [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (h : IsLatIn ⊤ (spanK z (M : Set C))) :
    Submodule.IsLattice F M := by
  have hinj : Function.Injective (coordMap z) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : z.symm ((1 : K) ⊗ₜ[F] x) = 0 := hx
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff F C x).1 h1
  refine ⟨?_, ?_⟩
  · have h1 : ((spanK z (M : Set C)).restrictScalars (𝓞 F)).FG := h.1.restrictScalars
    have h2 : M.map ((coordMap z).restrictScalars (𝓞 F)) ≤ (spanK z (M : Set C)).restrictScalars (𝓞 F) := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_spanK z hx
    exact Submodule.fg_of_fg_map_injective ((coordMap z).restrictScalars (𝓞 F)) hinj (h1.of_le h2)
  · refine Submodule.baseChange_injective (A := K) ?_
    rw [Submodule.baseChange_top, Submodule.baseChange_span, eq_top_iff]
    intro y _
    have h2 := h.2
    unfold spanK at h2
    rw [Submodule.span_span_of_tower] at h2
    have h3 : z.symm y ∈ Submodule.span K ((fun f : C => z.symm (1 ⊗ₜ[F] f)) '' (M : Set C)) := h2 ▸ Submodule.mem_top
    have h4 := Submodule.mem_map_of_mem (f := z.toLinearMap) h3
    rw [Submodule.map_span, ← Set.image_comp] at h4
    simp only [Function.comp_def, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h4
    exact h4

theorem exists_rem_of_concl {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j) (S : WeightAlgebra.Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (a b c d : ℝ)
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (hM : IsLatIn ⊤ (spanK z (B.Mlat j ka : Set _)))
    (hC : WeightAlgebra.Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (n : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (e : ℕ), (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e →
        ∀ W : Submodule K (Fin n → K),
          (lix v (cut W (spanK z (B.Mlat j ka : Set _))) (cut W (spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T})) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  have hM' := isLattice_of_spanK z _ hM
  have hn : X.rk ka (B.Mlat j ka) = n := by
    unfold WeightAlgebra.PJ.rk
    rw [hM'.span_eq_top, finrank_top]
    have := z.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_fin_fun] at this
    exact this.symm
  let Q : Formalism.MainNotions.Gaps.LocalGlobalPassage.Run D B P6 := ⟨j, X, S, ka, wL, wF, T, nus, X.rk ka (B.Mlat j ka) * a * b * c * d⟩
  obtain ⟨r, h0, h1, h2, h3⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.l2 Q (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1 la)
    (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1b la) (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1c la) hM' hC
  have hβ : Q.β = (n : ℝ) * (a * b * c * d) := by
    change (X.rk ka (B.Mlat j ka) : ℝ) * a * b * c * d = _
    rw [hn]
    ring
  refine ⟨fun v => (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * r (v.under (𝓞 B.KO)),
    fun v => mul_nonneg (Nat.cast_nonneg _) (h0 _),
    fun S' => (Formalism.MainNotions.Gaps.LocalGlobalPassage.l4 r h0 h1 S').trans (h2.trans hβ.le), ?_⟩
  intro v e he W
  have hpl : placeBelow (K := B.KO) v = v.under (𝓞 B.KO) := rfl
  have hram : ramOver (K := B.KO) v = v.asIdeal.ramificationIdx (𝓞 B.KO) := Formalism.MainNotions.Gaps.LocalGlobalPassage.ram_eq v
  obtain ⟨h4, h5⟩ := h3 (v.under (𝓞 B.KO))
  have hTh : Formalism.MainNotions.Gaps.LocalGlobalPassage.up (coordMap z) (Q.M0 ⊓ Q.Th0) ≤ spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T} :=
    Submodule.span_mono (Set.image_mono fun f hf => hf.2)
  exact Formalism.MainNotions.Gaps.LocalGlobalPassage.l5 (coordMap z) (coordMap_linearIndependent z) (coordMap_span z) Q.M0 (Q.M0 ⊓ Q.Th0) hM'.fg
    hM'.span_eq_top h4 inf_le_left v e (r (v.under (𝓞 B.KO))) (ramOver (K := B.KO) v * e)
    (by rw [hram]; push_cast; rfl) (h5 e (by rw [Int.cast_natCast, ← hpl]; exact he)) _ hTh W

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R) (h : ∀ a : R, s.star a = t.star a) : s = t := by
  obtain @⟨@⟨@⟨⟨f⟩, _⟩, _⟩, _⟩ := s
  obtain @⟨@⟨@⟨⟨g⟩, _⟩, _⟩, _⟩ := t
  obtain rfl : f = g := funext h
  rfl

theorem exists_rem_of_tie {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} {X : WeightAlgebra.PJ D B P6 j}
    {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ}
    {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {a b c d : ℝ}
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {v₁ : HeightOneSpectrum (𝓞 K)} {i : Bs.J}
    {z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka} {act : P → B.Cusp j ka → B.Cusp j ka}
    (ht : FormTieK X hinj EX p ka wL wF T O v₁ i z act) (hM : IsLatIn ⊤ (O.Ms i))
    (hC : WeightAlgebra.Concl X (scalOfP B hinj EX p ka wL wF T) ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (O.nZ i : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)), FormTieK X hinj EX p ka wL wF T O v i z act →
        ∀ e : ℕ, (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e → ∀ W : Submodule K (Fin (O.nZ i) → K),
          (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  obtain ⟨ρ, h0, h1, h2⟩ := exists_rem_of_concl X _ ka wL wF T nus a b c d z (ht.Ms_eq ▸ hM) hC
  refine ⟨ρ, h0, h1, fun v hv e he W => ?_⟩
  rw [hv.Ms_eq, hv.Th_eq]
  exact h2 v e he W

theorem nusR_le_eLam {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D)
    (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    letI := T.Q.H.starRing
    (Tp.TO : ℝ) * GlobalTheory.RunJoin.nusR h j (lR Tp hK j) la ≤
      ((GlobalTheory.RunDepth.depOf T.toCore EX Tp hK).Q.eLam (ramOverZ la)
        (nuStarAt (Xo := T.Q.Xo j) (c := T.Q.c) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) la j) (resCharOf la) : ℝ) := by
  have hn := GlobalTheory.RunDepthScale.nusOf_eq_ram_mul_nuStarAt D L Pm Tp hK T h EX j hj la
  refine le_trans (le_of_eq ?_) (DepPage.le_eLam _ _ _ _)
  refine (congrArg (fun t => (Tp.TO : ℝ) * t) hn).trans ?_
  rw [← mul_assoc, mul_comm (Tp.TO : ℝ)]
  rfl

set_option maxHeartbeats 1000000 in

theorem hasIndexBound_of_runs : ∀ CK : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → RunsHold Tp hK EX CK r → LeafSup O → LeafSpan O → O.b = L.sc.b → HasIndexBound O := by
  intro CK D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO _ _ hR hS hSp hb
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hO.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  let _ := hostAlg D
  obtain rfl : st = J.toCore.Q.H.starRing := starRing_eq _ _ hd.star_eq
  let _ := J.toCore.Q.H.starRing
  let _ : ∀ s : RunData J, Algebra s.full.J.Q.c.F D.what₂.LL := fun _ => inst
  let _ : ∀ (s : RunData J) (h : LawsP s.full.toTop), Algebra (recB h.toLawsCore).KO D.what₂.LL := fun _ _ => inst
  have key : ∀ (q : Prop) (i : Fin D.R.m), ∃ ρ : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ, (∀ v, 0 ≤ ρ v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)),
        ∑ v ∈ S', Formalism.DivisionValues.lw v * ρ v ≤ (O.nZ i : ℝ) * (D.R.f * D.R.m * L.sc.b * L.de2)) ∧
      ∀ v, (Formalism.EigenvalueLevelCeiling.plc v = D.host.pde ↔ q) → ∀ W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL),
        (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) + ρ v := by
    intro q i
    by_cases hq : ∃ v₁ : HeightOneSpectrum (𝓞 D.what₂.LL), (Formalism.EigenvalueLevelCeiling.plc v₁ = D.host.pde ↔ q)
    · obtain ⟨v₁, hv₁⟩ := hq
      obtain ⟨ρ, h0, h1, h2⟩ := @exists_rem_of_tie D (recB hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inst _ _ _ _ _ _ _ _ _ _ _ _ (ht v₁ i).1.toFormTieK (hS i).1
        (hR v₁ (hO.ok.laws v₁).p hinj ((i : ℕ) + 1) (inR_succ i)).2
      refine ⟨ρ, h0, h1, fun v hv W => ?_⟩
      have e1 : r.used v = r.used v₁ := by
        unfold TwoRuns.used
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have e2 : ownAt D v = ownAt D v₁ := by
        unfold ownAt
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have h3 := (ht v i).1.toFormTieK
      have h4 := (hO.ok.laws v).p
      rw [hd.E_eq v i]
      refine h2 v ?_ _ (nusR_le_eLam Tp hK EX (r.used v₁).full.toTop (hO.ok.laws v₁).p _ (inR_succ i) _) W
      have h5 : ∀ (s : RunData J) (h' : LawsP s.full.toTop) (p' : ℕ), s = r.used v₁ → p' = ownAt D v₁ →
          letI : Algebra (recB h'.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ h' ((i : ℕ) + 1) (inR_succ i)) hinj EX p' (kaR Tp hK ((i : ℕ) + 1)) (lR Tp hK ((i : ℕ) + 1))
            (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) →
          letI : Algebra (recB (hO.ok.laws v₁).p.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ (hO.ok.laws v₁).p ((i : ℕ) + 1) (inR_succ i)) hinj EX (ownAt D v₁) (kaR Tp hK ((i : ℕ) + 1))
            (lR Tp hK ((i : ℕ) + 1)) (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) := by
        rintro _ _ _ rfl rfl h
        exact h
      exact h5 _ h4 _ e1 e2 h3
    · refine ⟨fun _ => 0, fun _ => le_rfl, fun S' => ?_, fun v hv => absurd ⟨v, hv⟩ hq⟩
      have h1 := L.thickDensity_pos
      have h2 : 0 < L.sc.b := Real.exp_pos _
      simp only [mul_zero, Finset.sum_const_zero]
      positivity
  choose ρ h0 h1 h2 using key
  rw [← hd.f_eq, ← hd.m_eq, ← hb] at h1
  choose a ha using fun (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Fin D.R.m) => Formalism.MainNotions.Gaps.LocalGlobalPassage.exists_vw_eq v (O.E v i)
  refine ⟨O.Th, a, fun v i => ρ False i v, fun v i => ρ True i v, L.de2, ?_, L.thickDensity_pos.le, L.thickDensity_le_one,
    fun v i => ⟨h0 _ i v, h0 _ i v⟩, fun i S' => ⟨h1 _ i S', h1 _ i S'⟩⟩
  have hloc : ∀ v (i : Fin D.R.m) (W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL)),
      (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) +
        (if Formalism.EigenvalueLevelCeiling.plc v = O.pde then ρ True i v else ρ False i v) := by
    intro v i W
    rw [hO.pde_eq]
    split_ifs with hv
    · exact h2 True i v (iff_true_intro hv) W
    · exact h2 False i v (iff_false_intro hv) W
  intro w hw
  exact ⟨fun i => ⟨((hSp w hw).1 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩,
    fun i => ⟨((hSp w hw).2 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩⟩

end GlobalTheory.BigOn

end
