import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardFramesMatchCompletedLatticesAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentSmulMemCompletedSelfDualLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.FrameTransport

theorem latMatch : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → V'.rank = V.rank ∧ ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), J * J' = 1 ∧ J' * J = 1 ∧ (∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ)) ∧ ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V' :=
  GlobalTheory.T.standardFrames_match_completedLattices_at_prime

theorem lamHat_idem : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V :=
  GlobalTheory.T.placeIdempotent_smul_mem_completedSelfDualLattice

theorem rect_conj_one {R : Type} [CommRing R] {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    {β : Matrix a b R} {β' : Matrix b a R} {γ : Matrix c b R} {γ' : Matrix b c R}
    (hb2 : β' * β = 1) (hg1 : γ * γ' = 1) : γ * β' * (β * γ') = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc β', hb2, Matrix.one_mul, hg1]

theorem rect_conj {R : Type} [CommRing R] {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    {β : Matrix a b R} {β' : Matrix b a R} {γ : Matrix c b R} {γ' : Matrix b c R} {K : Matrix b b R}
    {M : Matrix a a R} {M' : Matrix c c R}
    (hb2 : β' * β = 1) (hg2 : γ' * γ = 1) (hM : M = β * K * β') (hM' : M' = γ * K * γ') :
    M' * (γ * β') = γ * β' * M := by
  rw [hM, hM']
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc γ' γ, hg2, Matrix.one_mul, ← Matrix.mul_assoc β' β, hb2, Matrix.one_mul]

variable {D : D7}

theorem conj_of_stdPsi {V V' : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {Q : principalLevelFrame.RowPsi V n} {Q' : principalLevelFrame.RowPsi V' n} (hQ : StdPsi hF Q) (hQ' : StdPsi hF Q') :
    ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
      (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
      J * J' = 1 ∧ J' * J = 1 ∧
      ∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ) := by
  obtain ⟨⟨β, β', hb1, hb2, hβ⟩, -⟩ := hQ
  obtain ⟨⟨γ, γ', hg1, hg2, hγ⟩, -⟩ := hQ'
  exact ⟨γ * β', β * γ', rect_conj_one hb2 hg1, rect_conj_one hg2 hb1,
    fun κ => rect_conj hb2 hg2 (hβ κ) (hγ κ)⟩

theorem suppF_of_stdPsi {V V' : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {Q : principalLevelFrame.RowPsi V n} {Q' : principalLevelFrame.RowPsi V' n} (hQ : StdPsi hF Q) (hQ' : StdPsi hF Q')
    (f : Formalism.L2.Theta.AE D) (κ : Formalism.AUTREP.GAf D.host.E n) :
    SuppF V f (Q.ψ κ) → SuppF V' f (Q'.ψ κ) := by
  obtain ⟨J, J', h1, -, hc⟩ := conj_of_stdPsi hQ hQ'
  rw [GlobalTheory.SphTrans.suppF_iff f (Q.into κ), GlobalTheory.SphTrans.suppF_iff f (Q'.into κ)]
  exact GlobalTheory.HeckeTrans.supp_conj h1 (hc κ)

theorem divAt_of_stdPsi {V V' : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {Q : principalLevelFrame.RowPsi V n} {Q' : principalLevelFrame.RowPsi V' n} (hQ : StdPsi hF Q) (hQ' : StdPsi hF Q')
    (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D) (hP : IsPrimeIdem P e f) (ϖ : D.host.E) (d : List ℤ)
    (κ : Formalism.AUTREP.GAf D.host.E n) :
    DivAt V e ϖ d (Q.ψ κ) → DivAt V' e ϖ d (Q'.ψ κ) := by
  rintro ⟨hlen, hdiv⟩
  obtain ⟨hr, J, J', h1, -, hc, hL⟩ := latMatch hF Q Q' hQ hQ' P e f hP
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  obtain ⟨hff, -⟩ := T3 P e f hP
  have hef : finPart D e * finPart D f = finPart D e := by
    rw [← RingHom.map_mul, GlobalTheory.SphTrans.mul_of_isPrimeIdem hP hff]
  exact ⟨hlen.trans hr.symm, GlobalTheory.SphTrans.div_conj hr (intAE D)
    (fun i => finPart D (incA D (ϖ ^ (d.getD i 0)))) hef h1 (hc κ) hL (lamHat_idem V P e f hP)
    (lamHat_idem V' P e f hP) hdiv⟩

end GlobalTheory.FrameTransport

namespace GlobalTheory.FrameTransport

variable {D : D7}

section Pre

variable {V : HSp D} {n : ℕ}

theorem pre_psi (Q : principalLevelFrame.RowPsi V n) (κ : Formalism.AUTREP.GAf D.host.E n) : principalLevelFrame.pre Q (Q.ψ κ) = κ := by
  have h : ∃ x, Q.ψ x = Q.ψ κ := ⟨κ, rfl⟩
  unfold principalLevelFrame.pre
  rw [dif_pos h]
  exact Q.inj h.choose_spec

theorem psi_pre (Q : principalLevelFrame.RowPsi V n) {γ : GA D V} (hγ : γ ∈ GfC V) : Q.ψ (principalLevelFrame.pre Q γ) = γ := by
  obtain ⟨h, rfl⟩ := Q.onto γ hγ
  rw [pre_psi]

theorem pre_of_not_mem (Q : principalLevelFrame.RowPsi V n) {γ : GA D V} (hγ : γ ∉ GfC V) : principalLevelFrame.pre Q γ = 1 := by
  unfold principalLevelFrame.pre
  rw [dif_neg]
  rintro ⟨x, rfl⟩
  exact hγ (Q.into x)

end Pre

variable {V V' : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {Q : principalLevelFrame.RowPsi V n} {Q' : principalLevelFrame.RowPsi V' n}

theorem ksph_iff (hQ : StdPsi hF Q) (hQ' : StdPsi hF Q') (κ : Formalism.AUTREP.GAf D.host.E n) :
    Q.ψ κ ∈ KsphC V ∅ ↔ Q'.ψ κ ∈ KsphC V' ∅ :=
  (hQ.2 κ).symm.trans (hQ'.2 κ)

theorem suppF_iff (hQ : StdPsi hF Q) (hQ' : StdPsi hF Q') (f : Formalism.L2.Theta.AE D) (κ : Formalism.AUTREP.GAf D.host.E n) :
    SuppF V f (Q.ψ κ) ↔ SuppF V' f (Q'.ψ κ) :=
  ⟨suppF_of_stdPsi hQ hQ' f κ, suppF_of_stdPsi hQ' hQ f κ⟩

theorem hyp_iff (hQ : StdPsi hF Q) (hQ' : StdPsi hF Q') (Pr : Pl D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n) :
    Q.ψ κ ∈ hyp V Pr ↔ Q'.ψ κ ∈ hyp V' Pr := by
  constructor
  · rintro ⟨h1, e, f, hp, hs⟩
    exact ⟨(ksph_iff hQ hQ' κ).1 h1, e, f, hp, (suppF_iff hQ hQ' f κ).1 hs⟩
  · rintro ⟨h1, e, f, hp, hs⟩
    exact ⟨(ksph_iff hQ hQ' κ).2 h1, e, f, hp, (suppF_iff hQ hQ' f κ).2 hs⟩

end GlobalTheory.FrameTransport

namespace GlobalTheory.FrameTransport

variable {D : D7}

theorem one_mem_KsphC (V : HSp D) : (1 : GA D V) ∈ KsphC V ∅ :=
  ⟨one_mem _, fun y => by rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec],
    fun v hv => absurd hv (Finset.notMem_empty v)⟩

theorem suppF_one (V : HSp D) (f : Formalism.L2.Theta.AE D) : SuppF V f (1 : GA D V) := by
  intro i j
  have : Formalism.L2.Theta.mt V 1 - 1 = 0 := sub_self _
  rw [this]
  exact mul_zero _

variable {V V' : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {Q : principalLevelFrame.RowPsi V n} {Q' : principalLevelFrame.RowPsi V' n}

theorem loc_iff (hQ : StdPsi hF Q) (hQ' : StdPsi hF Q') (f : Formalism.L2.Theta.AE D) (κ : Formalism.AUTREP.GAf D.host.E n) :
    Q.ψ κ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ Q'.ψ κ ∈ {k | k ∈ KsphC V' ∅ ∧ SuppF V' f k} :=
  and_congr (ksph_iff hQ hQ' κ) (suppF_iff hQ hQ' f κ)

open Classical in

theorem sphOp_image (hQ : StdPsi hF Q) (hQ' : StdPsi hF Q') {Pr : Pl D.host.E} {d : List ℤ} {B : Finset (GA D V)}
    (hB : SphOp V Pr d B) : SphOp V' Pr d (B.image fun γ => Q'.ψ (principalLevelFrame.pre Q γ)) := by
  obtain ⟨e, f, ϖ, α, -, hpi, hϖ1, hϖ2, hd, -, -, hsα, hdiv, hsR, hcos⟩ := hB
  have hK : ∀ k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k}, k ∈ GfC V := fun k hk => hk.1.1
  have hK' : ∀ k ∈ {k | k ∈ KsphC V' ∅ ∧ SuppF V' f k}, k ∈ GfC V' := fun k hk => hk.1.1
  have h1 : (1 : GA D V) ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := ⟨one_mem_KsphC V, suppF_one V f⟩

  have hαf : α ∈ GfC V := by
    obtain ⟨γ, ⟨hγ, -⟩, -⟩ := hcos.2 α ⟨1, h1, 1, h1, by simp⟩
    obtain ⟨hγf, k₁, hk₁, k₂, hk₂, hγe⟩ := hcos.1 γ hγ
    have : α = k₁⁻¹ * γ * k₂⁻¹ := by rw [hγe]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (hK k₁ hk₁)) hγf) (inv_mem (hK k₂ hk₂))
  set a := principalLevelFrame.pre Q α with ha
  have hαa : Q.ψ a = α := psi_pre Q hαf
  refine ⟨e, f, ϖ, Q'.ψ a, fun v hv => absurd hv (Finset.notMem_empty v), hpi, hϖ1, hϖ2, hd,
    fun _ _ => Iff.rfl, fun _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact suppF_of_stdPsi hQ hQ' f a (hαa ▸ hsα)
  · exact divAt_of_stdPsi hQ hQ' Pr e f hpi ϖ d a (hαa ▸ hdiv)
  · intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hγ'
    have hγf := (hcos.1 γ hγ).1
    exact suppF_of_stdPsi hQ hQ' f _ ((psi_pre Q hγf).symm ▸ hsR γ hγ)
  · intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hγ'
    obtain ⟨hγf, k₁, hk₁, k₂, hk₂, hγe⟩ := hcos.1 γ hγ
    refine ⟨Q'.into _, Q'.ψ (principalLevelFrame.pre Q k₁), (loc_iff hQ hQ' f _).1 ((psi_pre Q (hK k₁ hk₁)).symm ▸ hk₁),
      Q'.ψ (principalLevelFrame.pre Q k₂), (loc_iff hQ hQ' f _).1 ((psi_pre Q (hK k₂ hk₂)).symm ▸ hk₂), ?_⟩
    have e1 : principalLevelFrame.pre Q γ = principalLevelFrame.pre Q k₁ * a * principalLevelFrame.pre Q k₂ := by
      apply Q.inj
      rw [psi_pre Q hγf, map_mul, map_mul, psi_pre Q (hK k₁ hk₁), psi_pre Q (hK k₂ hk₂), hαa, hγe]
    rw [e1, map_mul, map_mul]
  · rintro x' ⟨k₁', hk₁', k₂', hk₂', rfl⟩
    obtain ⟨c₁, rfl⟩ := Q'.onto k₁' (hK' _ hk₁')
    obtain ⟨c₂, rfl⟩ := Q'.onto k₂' (hK' _ hk₂')
    have hc₁ := (loc_iff hQ hQ' f c₁).2 hk₁'
    have hc₂ := (loc_iff hQ hQ' f c₂).2 hk₂'
    obtain ⟨γ, ⟨hγ, hγx⟩, huniq⟩ := hcos.2 (Q.ψ c₁ * α * Q.ψ c₂) ⟨_, hc₁, _, hc₂, rfl⟩
    have hγf := (hcos.1 γ hγ).1
    have key : ∀ g : Formalism.AUTREP.GAf D.host.E n,
        (Q.ψ g)⁻¹ * (Q.ψ c₁ * α * Q.ψ c₂) ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔
        (Q'.ψ g)⁻¹ * (Q'.ψ c₁ * Q'.ψ a * Q'.ψ c₂) ∈ {k | k ∈ KsphC V' ∅ ∧ SuppF V' f k} := by
      intro g
      have := loc_iff hQ hQ' f (g⁻¹ * (c₁ * a * c₂))
      simp only [map_mul, map_inv, hαa] at this
      exact this
    refine ⟨Q'.ψ (principalLevelFrame.pre Q γ), ⟨Finset.mem_image_of_mem _ hγ, ?_⟩, ?_⟩
    · exact (key _).1 (by rw [psi_pre Q hγf]; exact hγx)
    · rintro δ' ⟨hδ', hδx⟩
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hδ'
      have hδf := (hcos.1 δ hδ).1
      have : δ = γ := huniq δ ⟨hδ, by rw [← psi_pre Q hδf]; exact (key _).2 hδx⟩
      rw [this]

def rreg (V : HSp D) : GA D V →* Module.End ℂ (GA D V → ℂ) where
  toFun k :=
    { toFun := fun F g => F (g * k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext F g; simp
  map_mul' a b := by ext F g; simp [mul_assoc]

end GlobalTheory.FrameTransport

namespace GlobalTheory.FrameTransport

variable {D : D7}

theorem sphOp_sub_GfC {V : HSp D} {Pr : Pl D.host.E} {d : List ℤ} {R : Finset (GA D V)} (hR : SphOp V Pr d R) :
    ∀ γ ∈ R, γ ∈ GfC V := by
  obtain ⟨e, f, ϖ, α, -, -, -, -, -, -, -, -, -, -, hcos⟩ := hR
  exact fun γ hγ => (hcos.1 γ hγ).1

variable {V V' : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {Q : principalLevelFrame.RowPsi V n} {Q' : principalLevelFrame.RowPsi V' n}

theorem heckeOperator_apply (Q : principalLevelFrame.RowPsi V n) (R : Finset (GA D V)) (x : Formalism.AUTREP.GAf D.host.E n → ℂ)
    (h : Formalism.AUTREP.GAf D.host.E n) : principalLevelFrame.Hecke₃ Q R x h = ∑ γ ∈ R, x (h * principalLevelFrame.pre Q γ) := by
  unfold principalLevelFrame.Hecke₃ principalLevelFrame.heckeG
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

open Classical in
theorem heckeOperator_image {B : Finset (GA D V)} (hB : ∀ γ ∈ B, γ ∈ GfC V) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) :
    principalLevelFrame.Hecke₃ Q B x = principalLevelFrame.Hecke₃ Q' (B.image fun γ => Q'.ψ (principalLevelFrame.pre Q γ)) x := by
  funext h
  rw [heckeOperator_apply, heckeOperator_apply, Finset.sum_image]
  · simp only [pre_psi]
  · intro a ha b hb hab
    have := congrArg (principalLevelFrame.pre Q') hab
    simp only [pre_psi] at this
    rw [← psi_pre Q (hB a ha), ← psi_pre Q (hB b hb), this]

theorem heckeOperator_eq_heckeAlgebraAction {Pr : Pl D.host.E} {d : List ℤ} {R : Finset (GA D V')}
    (hR : SphOp V' Pr d R) (x : Formalism.AUTREP.GAf D.host.E n → ℂ)
    (hx : ∀ κ, Q'.ψ κ ∈ hyp V' Pr → Formalism.L2.NG.rt D.host.E n κ x = x) :
    principalLevelFrame.Hecke₃ Q' R x = fun h => GlobalTheory.Hk3.opOf (rreg V') Pr (Finsupp.single d 1) (fun g => x (principalLevelFrame.pre Q' g)) (Q'.ψ h) := by
  have hu : ∀ k ∈ hyp V' Pr, rreg V' k (fun g => x (principalLevelFrame.pre Q' g)) = fun g => x (principalLevelFrame.pre Q' g) := by
    intro k hk
    have hkf : k ∈ GfC V' := hk.1.1
    obtain ⟨c, rfl⟩ := Q'.onto k hkf
    funext g
    show x (principalLevelFrame.pre Q' (g * Q'.ψ c)) = x (principalLevelFrame.pre Q' g)
    by_cases hg : g ∈ GfC V'
    · obtain ⟨g0, rfl⟩ := Q'.onto g hg
      rw [← map_mul, pre_psi, pre_psi]
      exact congrFun (hx c hk) g0
    · have hgk : g * Q'.ψ c ∉ GfC V' := fun h' => hg (by
        have : g = g * Q'.ψ c * (Q'.ψ c)⁻¹ := by group
        rw [this]; exact mul_mem h' (inv_mem hkf))
      rw [pre_of_not_mem Q' hg, pre_of_not_mem Q' hgk]
  have key := ((GlobalTheory.SphLabelOps.label_operators V' Pr).1 d R hR).2 (GA D V' → ℂ) (rreg V')
    (fun g => x (principalLevelFrame.pre Q' g)) hu
  funext h
  rw [← key, heckeOperator_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  show x (h * principalLevelFrame.pre Q' γ) = x (principalLevelFrame.pre Q' (Q'.ψ h * γ))
  rw [← psi_pre Q' (sphOp_sub_GfC hR γ hγ), ← map_mul, pre_psi, pre_psi]

theorem sph_eigen_frame_indep : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ Pr d, (∀ κ, Q.ψ κ ∈ hyp V Pr ↔ Q'.ψ κ ∈ hyp V' Pr) ∧ ∀ B B', SphOp V Pr d B → SphOp V' Pr d B' → ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ κ, Q.ψ κ ∈ hyp V Pr → Formalism.L2.NG.rt D.host.E n κ x = x) → principalLevelFrame.Hecke₃ Q B x = principalLevelFrame.Hecke₃ Q' B' x := by
  intro D V V' n hF Q Q' hQ hQ' Pr d
  refine ⟨hyp_iff hQ hQ' Pr, ?_⟩
  intro B B' hB hB' x hx
  have hx' : ∀ κ, Q'.ψ κ ∈ hyp V' Pr → Formalism.L2.NG.rt D.host.E n κ x = x :=
    fun κ hk => hx κ ((hyp_iff hQ hQ' Pr κ).2 hk)
  rw [heckeOperator_image (Q' := Q') (sphOp_sub_GfC hB) x, heckeOperator_eq_heckeAlgebraAction (sphOp_image hQ hQ' hB) x hx',
    heckeOperator_eq_heckeAlgebraAction hB' x hx']

end GlobalTheory.FrameTransport
