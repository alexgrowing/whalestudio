import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIoLFRecIff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IoConj

section General

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {c : Coeff l} (j : c.F →+* c.F) {n : ℕ}

theorem gaStar_map (hj : ∀ σ x, j (embF c σ x) = embF c σ x) (ga : Matrix (Fin n) (Fin n) E)
    (P : MvPolynomial (LtN Dw n) c.F) :
    Formalism.L2.Pj.gaStar c ga (map j P) = map j (Formalism.L2.Pj.gaStar c ga P) := by
  induction P using MvPolynomial.induction_on with
  | C x => rw [map_C, Formalism.L2.Pj.gaStar, aeval_C, aeval_C, algebraMap_eq, map_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [Formalism.L2.Pj.gaStar, aeval_X, letB, map_sum, map_mul, map_C, map_X, hj]

theorem pG_map (a : (E →+* ℂ) × ℕ → ℕ) : map j (pG (Dw := Dw) c a n) = pG (Dw := Dw) c a n := by
  have h : ∀ s i hi col, minorPolynomial (Dw := Dw) (n := n) c s i hi col = map j (minorPolynomial c s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  symm
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero]

theorem rhoM_map (hj : ∀ σ x, j (embF c σ x) = embF c σ x) {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))
    (lam : Ix → DomWeight n) (ga : Matrix (Fin n) (Fin n) E) (v v' : VVc c lam)
    (h : (v' : Pol c.F Ix n) = map j (v : Pol c.F Ix n)) :
    (rhoM c (fun t => embF c (pl t)) lam ga v' : Pol c.F Ix n) =
      map j (rhoM c (fun t => embF c (pl t)) lam ga v : Pol c.F Ix n) := by
  unfold rhoM
  split_ifs with hg
  · show actP lam _ (v' : Pol c.F Ix n) = map _ (actP lam _ (v : Pol c.F Ix n))
    rw [h]
    refine GlobalTheory.IoExtend.polyAction_map _ lam _ _ (fun t => ?_) _
    refine Matrix.ext fun a b => ?_
    exact (hj (pl t) _).symm
  · simp

theorem exists_stable (hj : ∀ σ x, j (embF c σ x) = embF c σ x) {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))
    (hpl : Function.Injective pl) (hin : ∀ σ, InPsi H σ ↔ ∃ t, σ = pl t)
    (lam : Ix → DomWeight n) (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam)
    (h : IoLFRec c (fun t => embF c (pl t)) lam a io hw) :
    ∃ N : Submodule c.F (VVc c lam), hw ∈ N ∧
      (∀ ga : Matrix (Fin n) (Fin n) E, gaᴴ * ga = 1 → ∀ v ∈ N, rhoM c (fun t => embF c (pl t)) lam ga v ∈ N) ∧
      ∀ v ∈ N, ∀ v' : VVc c lam, (v' : Pol c.F Ix n) = map j (v : Pol c.F Ix n) → io v' = map j (io v) := by
  obtain ⟨hok, cga, h⟩ := h
  let e : Ix ≃ GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights.Psi H := Equiv.ofBijective (fun t => ⟨pl t, (hin _).2 ⟨t, rfl⟩⟩)
    ⟨fun s t hst => hpl (congrArg Subtype.val hst), fun σ => by
      obtain ⟨t, ht⟩ := (hin σ.1).1 σ.2
      exact ⟨t, Subtype.ext ht.symm⟩⟩
  obtain ⟨ha, d, -, hd⟩ := GlobalTheory.LFCompare.pins_of_ioLF Dw c n e a lam io hw cga hok h
  have hcga : ∀ ga : Matrix (Fin n) (Fin n) E, gaᴴ * ga = 1 → j (cga ga) = cga ga := fun ga hga => by
    rw [hd ga hga, GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights.vacChar, map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [map_zpow₀]
    exact congrArg (· ^ _) (hj _ _)
  obtain ⟨-, -, -, h4, -, -, h7, -⟩ := h
  let up : VVc c lam → VVc c lam := fun v => ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV j lam _ v.2⟩
  refine ⟨
    { carrier := {v | io (up v) = map j (io v)}
      add_mem' := fun {v w} hv hw' => ?_
      zero_mem' := ?_
      smul_mem' := fun s v hv => ?_ }, ?_, fun ga hga v hv => ?_, fun v hv v' hv' => ?_⟩
  · have e1 : up (v + w) = up v + up w := Subtype.ext (map_add (map j) _ _)
    show io (up (v + w)) = _
    rw [e1, map_add, map_add, map_add, show io (up v) = _ from hv, show io (up w) = _ from hw']
  · have e1 : up 0 = 0 := Subtype.ext (map_zero (map j))
    show io (up 0) = _
    rw [e1, map_zero, map_zero]
  · have e1 : up (s • v) = j s • up v := Subtype.ext (GlobalTheory.IoExtend.map_smul' j s _)
    show io (up (s • v)) = _
    rw [e1, map_smul, map_smul, GlobalTheory.IoExtend.map_smul', show io (up v) = _ from hv]
  · have e1 : up hw = hw := by
      apply Subtype.ext
      show map j (hw : Pol c.F Ix n) = _
      rw [show (hw : Pol c.F Ix n) = _ from hok, GlobalTheory.Proof.TensorMapDescent.map_ten]
      simp only [Formalism.L2.DIV.map_extremal]
    show io (up hw) = _
    rw [e1, h7, pG_map]
  · have e1 : up (rhoM c (fun t => embF c (pl t)) lam ga v) = rhoM c (fun t => embF c (pl t)) lam ga (up v) :=
      Subtype.ext (rhoM_map j hj pl lam ga v (up v) rfl).symm
    show io (up _) = _
    rw [e1, h4 ga hga, h4 ga hga, GlobalTheory.IoExtend.map_smul', hcga ga hga, show io (up v) = _ from hv, gaStar_map j hj]
  · rw [show v' = up v from Subtype.ext hv']
    exact hv

theorem eq_top_of_span {K X M : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup M] [Module ℂ M]
    {σ : K →+* ℂ} (c0 : X →ₛₗ[σ] M)
    (hli : ∀ (m : ℕ) (b : Fin m → X), LinearIndependent K b → LinearIndependent ℂ (fun k => c0 (b k)))
    (N : Submodule K X) (hN : Submodule.span ℂ (c0 '' (N : Set X)) = ⊤) : N = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := N.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
  obtain ⟨B, hB⟩ := GlobalTheory.AdTh.PhaseMap.exists_ext (N := ℂ) c0 hli
    { toFun := fun v => σ (f v)
      map_add' := fun v w => by rw [map_add, map_add]
      map_smul' := fun s v => by rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul] }
  replace hB : ∀ v, B (c0 v) = σ (f v) := hB
  have h1 : Submodule.span ℂ (c0 '' (N : Set X)) ≤ LinearMap.ker B := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show B (c0 v) = 0
    rw [hB, show f v = 0 from hf hv, map_zero]
  refine hf0 (LinearMap.ext fun v => ?_)
  have h2 : B (c0 v) = 0 := h1 (hN ▸ Submodule.mem_top)
  rw [hB] at h2
  exact (map_eq_zero σ).1 h2

end General

section Main

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000 in

theorem io_map_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) → M.io x' = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io x) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hfw i Tp tup O hO τ ta hta hfix x x' hx
  obtain ⟨fw⟩ := hfw
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hθ : IsInfFam R.θ := hR.models.inf
  have hc : (R.cV i).Is := hR.models.cV i
  have hP := (GlobalTheory.AdTh.RecPair.isPair_record_ofCore D G Pl0 T0 A _ R F hR i A.μ0 hO.lift.std).1
  obtain ⟨n1, n2, -, n4⟩ := GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofCore D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hO
  obtain ⟨-, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) (R.cV i) (hR.models.vpos i) hP.sigV hc
  obtain ⟨-, -, w1, -, -⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hj : ∀ σ y, (ta : O.c'.F →+* O.c'.F) (embF O.c' σ y) = embF O.c' σ y := fun σ y =>
    Subtype.ext ((hta _).trans (hfix.host σ y))
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_stable (ta : O.c'.F →+* O.c'.F) hj (tauE D) (GlobalTheory.SmoothForms.RealPts.tauE_injective D) w1
    (lamV D i) (wtA (κ i)) O.io O.hw hO.io
  haveI : FiniteDimensional O.c'.F (VsV D i O.c'.F) := Module.Finite.of_basis (Formalism.L2.DIV.bVV O.c'.F (lamV D i))
  have htop : N = ⊤ := by
    refine eq_top_of_span O.c0' n4 N ((r2 _ fun γ => ?_).resolve_left fun h0 => ?_)
    · obtain ⟨γE, -, -, h1, -, -, -, h5, -⟩ := GlobalTheory.AdTh.PhaseMap.rat_parts hθ hP.std γ
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨_, hN2 _ h5 v hv, n2 γ γE h1 v⟩
    · have h1 : O.c0' O.hw ∈ Submodule.span ℂ (O.c0' '' (N : Set _)) := Submodule.subset_span ⟨_, hN1, rfl⟩
      rw [h0, Submodule.mem_bot] at h1
      rw [h1, norm_zero] at n1
      exact zero_ne_one n1
  exact hN3 x (htop ▸ Submodule.mem_top) x' hx

end Main

end GlobalTheory.IoConj
