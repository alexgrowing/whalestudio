import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumValuesUnitOfClassSumValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVacuumMultiplierConstantPerLatticeStatement

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CcEx

noncomputable section

open GlobalTheory.ClsVal.Cmp

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

def anFibBas {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
    {X : Data E r} {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw}
    {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ} (h : ∀ z w, hx X bas' idx x z w = hx X bas idx x z w)
    (A : AnFib X bas idx e x L y) : AnFib X bas' idx e x L y where
  ex := A.ex
  ex_add := A.ex_add
  ex_onto := A.ex_onto
  ex_ker := A.ex_ker
  ex_lin := A.ex_lin
  hol := A.hol
  der := A.der
  fr := A.fr
  fr_hol := A.fr_hol
  fr_ne := A.fr_ne
  fr_g := A.fr_g
  fr_0 := A.fr_0
  χ := A.χ
  χ_norm := A.χ_norm
  fr_per v hv j z hz := by rw [h, h]; exact A.fr_per v hv j z hz

theorem coord_eq {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas)
    {x : Frame X.Ψ r} (hx' : x ∈ X.dom) {p q : X.Ψ × Fin r} (h : ∀ v, per X x v p = per X x v q) : p = q := by
  obtain ⟨i, rfl⟩ := idx.surjective p
  obtain ⟨j, rfl⟩ := idx.surjective q
  have hsp := ((hx_laws E r X g bas idx 0 hs Even.zero x hx').2.2.2.2.2.2.1 ⊤ (by simp)).1
  have key : ∀ z : Fin g → ℂ, z i = z j := by
    intro z
    have hz : z ∈ Submodule.span ℝ (pv X idx x '' ((⊤ : Lt E r) : Set (Fin r → E))) := hsp ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨v, -, rfl⟩ := hz; exact h v
    | zero => rfl
    | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]
    | smul a b _ hb => simp only [Pi.smul_apply, hb]
  by_contra hne
  have hij : j ≠ i := fun e => hne (by rw [e])
  have := key (Pi.single i 1)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
  exact one_ne_zero this

variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem genReads_change (U : Unf Xo c σ r) (k : U.Comp) {g g' : ℕ}
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx' : Fin g' ≃ (U.X k).Ψ × Fin r) (e' : Fin g' ≃ Lt1 Dw)
    (hs : IsSympl (U.X k) bas) (hs' : IsSympl (U.X k) bas') (hi : IdxIs c σ (U.X k) idx e) (hi' : IdxIs c σ (U.X k) idx' e')
    (x : (U.X k).dom) (hon : IsONFr (U.X k) x.1) (ϑ' : (Fin g' → ℂ) → ℂ) (h : GenReads U k bas' idx' e' x ϑ') :
    ∃ ϑ, GenReads U k bas idx e x ϑ ∧ ∀ u : (U.X k).Ψ × Fin r → ℂ, ϑ' (u ∘ idx') = ϑ (u ∘ idx) ∧
      hx (U.X k) bas' idx' x.1 (u ∘ idx') (u ∘ idx') = hx (U.X k) bas idx x.1 (u ∘ idx) (u ∘ idx) := by
  have hg : g' = g := by simpa using Fintype.card_congr (idx'.trans idx.symm)
  subst hg
  obtain ⟨π, rfl⟩ : ∃ π : Equiv.Perm (Fin g'), e' = π.trans e := ⟨e'.trans e.symm, by ext1; simp⟩
  have hidx : idx' = π.trans idx := by
    ext1 j
    exact coord_eq idx hs x.2 fun v => (hi'.1 x.1 v j).trans (hi.1 x.1 v (π j)).symm
  subst hidx
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨A, hA⟩ := h
  have hb : ∀ z w, hx (U.X k) bas idx x.1 z w = hx (U.X k) bas' idx x.1 z w := fun z w => by
    rw [(hx_of_isONFr E r g' 0 _ bas idx hs Even.zero _ hon).2.2, (hx_of_isONFr E r g' 0 _ bas' idx hs' Even.zero _ hon).2.2]
  refine ⟨ϑ' ∘ ren π, ⟨anFibBas hb (anFibRen π A), fun j z pt h1 h2 h3 => hA j (ren π z) pt h1 h2 h3⟩, fun u => ⟨rfl, ?_⟩⟩
  rw [hb]
  exact hx_ren _ bas' idx π x.1 (u ∘ idx) (u ∘ idx)

end Gen

theorem thA_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g) (x : Frame X.Ψ r)
    (z : Fin n → Fin g → ℂ) : thA X bas idx (a • φ) x z = a * thA X bas idx φ x z := by
  simp only [thA, SW.thS, show ∀ y, (a • φ) y = a * φ y from fun _ => rfl, _root_.mul_assoc, tsum_mul_left]
  ring

theorem exists_ccIs_of_pair (hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {V W : HSp D} {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) {mu : GA D W → ℂ} (hmu : MuVal W χV mu) (hmuQ : ∀ γ ∈ GQ W, ∀ h, mu (γ * h) = mu h)
    {r : ℕ} (hr : W.rank = r) {H : Geo.Tor.Host D.host.E} (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : IsUnf U) (hr1 : 1 ≤ r) (hA : l.A = 1) {a : (D.host.E →+* ℂ) × ℕ → ℕ} (hdom : Dom a V.rank)
    {ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (hV0 : V.rank ≠ 0) (h1 : (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V) (h2 : (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W)
    (h3 : IsSelfDualC V ΛV) (h4 : IsSelfDualC W ΛW)
    (h5 : (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hmod : ∀ k, IsMod W hr (U.X k)) (hon : ∀ k, IsONFr (U.X k) (fun τ => x₀ τ.1))
    (hinv : ∀ k, IsInvOf W hr (U.X k) (fun τ => x₀ τ.1) s) {f : WO V W → ℂ}
    (hf : IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) : ∃ cc, CcIs θ V W hr U dict mu x₀ om f cc := by
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  have hw : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hw' : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  have key : ∀ k : U.Comp, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ (h : GA D W) (x : (U.X k).dom), latR hr (latG W h) = (U.X k).Λ →
      x.1 = frMove θ W hr (U.X k) h (fun τ => x₀ τ.1) → ∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ)
      (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X k) bas → IdxIs c σ (U.X k) idx e →
      ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads U k bas idx e x ϑ → ∀ w : WO V W, w.map (finPart D) = 0 →
        om (1, h) f w = a * mu h *
          cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (U.X k) bas idx x.1
            (zOf θ V W hr (U.X k) idx x.1 w b) (zOf θ V W hr (U.X k) idx x.1 w b)) *
          ∏ b, ϑ (zOf θ V W hr (U.X k) idx x.1 w b) := by
    intro k
    have hsd : SelfD (U.X k) (U.X k).Λ := (uw_lattice _ H Dw l Xo c σ _ _ hσ hU' hr1 Wt k).2.1
    obtain ⟨Dc, -, -⟩ := exists_dic _ H Dw l c σ _ Wt.g V.rank (U.X k) a Wt.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hsd hdom
    have hi : IdxIs c σ (U.X k) Dc.idx Dc.e := ⟨Dc.per_eq, Dc.ty_eq⟩
    obtain ⟨v, hv⟩ := (TensVac.vacua _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hP.even _ hw hw' _ hsd 1 _
      (Base.stdL_mem_Vset V.rank 1)).1
    obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.pow_generator_eq_const_mul_vacuum_theta hci _ H Dw l Xo c σ r U hσ hU hr1 hA k V.rank _ Dc.bas Dc.idx Dc.e hP.even
      Dc.sympl hi v hv
    obtain ⟨κ, -, hκ, hrd⟩ := GlobalTheory.T.exists_vacuum_multiplier_constant_per_lattice D ψ θ V W χV χW om hP mu hmu r _ hr (U.X k) Dc.bas Dc.idx (hmod k) Dc.sympl H hrt
      ΛV ΛW hV0 h1 h2 h3 h4 h5 hsd _ s (hon k) (hinv k) f hf v hv
    refine ⟨κ / C, ?_, fun h x hL hxe g bas idx e hs hie ϑ' hϑ' w hw0 => ?_⟩
    · obtain ⟨hd, hu, -⟩ := hx_of_isONFr _ r _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ (hon k)
      obtain ⟨⟨ϑ, hϑ⟩, hall⟩ := hC ⟨_, hd⟩ hu
      obtain ⟨t1, t2, t3⟩ := hall ϑ hϑ
      rw [norm_div, ← hκ _ hd hu ϑ C t1 t2 t3, div_self (norm_ne_zero_iff.2 hC0)]
    · obtain ⟨hon', -, hread⟩ := hrd h hL
      rw [← hxe] at hon' hread
      obtain ⟨-, hu, -⟩ := hx_of_isONFr _ r _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ hon'
      obtain ⟨ϑ, hϑ, hch⟩ := genReads_change U k Dc.bas Dc.idx Dc.e bas idx e Dc.sympl hs hi hie x hon' ϑ' hϑ'
      have t3 := ((hC x hu).2 ϑ hϑ).2.2 (zOf θ V W hr (U.X k) Dc.idx x.1 w)
      have e1 : ∏ b, ϑ' (zOf θ V W hr (U.X k) idx x.1 w b) = ∏ b, ϑ (zOf θ V W hr (U.X k) Dc.idx x.1 w b) :=
        Finset.prod_congr rfl fun b _ => (hch _).1
      have e2 : ∑ b, hx (U.X k) bas idx x.1 (zOf θ V W hr (U.X k) idx x.1 w b) (zOf θ V W hr (U.X k) idx x.1 w b) =
          ∑ b, hx (U.X k) Dc.bas Dc.idx x.1 (zOf θ V W hr (U.X k) Dc.idx x.1 w b)
            (zOf θ V W hr (U.X k) Dc.idx x.1 w b) :=
        Finset.sum_congr rfl fun b _ => (hch _).2
      rw [hread w hw0, e1, e2, t3, thA_smul']
      field_simp
  choose cc hcc hkey using key
  refine ⟨cc, hcc, fun h γ hat hx' g bas idx e hs hi ϑ hϑ w hw0 => ?_⟩
  rw [← hmuQ γ hat.1 h]
  exact hkey _ (γ * h) ⟨_, hx'⟩ hat.2.1 hat.2.2 g bas idx e hs hi ϑ hϑ w hw0

theorem exists_ccIs : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro hci D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup O hO
  have hs0 : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.theta_pair_characters_at_level D G Pl0 T0 A _ R F hC i A.μ0 hO.lift.std
  have hM := GlobalTheory.T.level_form_compat_base_embedding D G Pl0 T0 A T R F κ v₀ hC hT i O.s0 hs0
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) O.s0 := by
    rw [hs0, chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC.lev.xi_base ▸ hC.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) O.s0 = W),
      MuVal W (T.chiW ((i : ℕ) + 1) O.s0) (castDict hV (T.mu ((i : ℕ) + 1) O.s0)) ∧ ∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) O.s0) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) O.s0) h := by
    intro W hV
    subst hV
    have hu := hT.laws.muUnit _ (inR i) _ hσ
    exact ⟨hT.laws.muVal _ (inR i) _ hσ, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl)⟩
  obtain ⟨hmu, hmuQ⟩ := hcast _ O.hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (O.dict 1).1
  exact exists_ccIs_of_pair hci hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt _ hσ (hT.laws.unf _ (inR i) _ hσ) hr1
    hT.laws.pins.2.1.2 hdom hV0 h1 h2 h3 h4 h5 _ _ (fun k => (hM k).1) (fun k => (hM k).2.1) (fun k => (hM k).2.2.1)
    (hC.thP.vP i A.μ0).1 _

end

end GlobalTheory.AdTh.CcEx
