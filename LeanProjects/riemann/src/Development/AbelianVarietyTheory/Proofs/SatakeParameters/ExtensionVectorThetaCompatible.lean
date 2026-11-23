import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameMemHyperspecialIffMaxCompactTrivOutStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardElementSplitPlaceLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHeckeSplitPlaceSetIffDoubleCosetStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigTransport

theorem frame_hyp : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → ∀ (sp : SplitPlace D.host.E)
    (κ : Formalism.AUTREP.GAf D.host.E n), Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w ↔ κ ∈ Umax D.host.E n ∧ TrivOutside {sp.v} κ := GlobalTheory.T.standardFrame_mem_hyperspecial_iff_maxCompact_trivOutside

theorem exists_std : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ →
    ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E),
      Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧
        Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧
        Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := GlobalTheory.T.standardElement_splitPlace_label

theorem tSet_dc : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k,
    ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧
      ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := GlobalTheory.T.mem_heckeSplitPlaceSet_iff_doubleCoset

theorem pairwise_lab (k m : ℕ) : List.Pairwise (fun a b : ℤ => b ≤ a) (List.replicate k 1 ++ List.replicate m 0) := by
  rw [List.pairwise_append]
  refine ⟨List.pairwise_replicate.2 (Or.inr le_rfl), List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩
  intro a ha b hb
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem isLab_std {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hs : GlobalTheory.NJoin.StdFrame hF Ps) (hn : V.rank = n) (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)) (hϖ : Formalism.AUTREP.IsUnif D.host.E sp.v ϖ)
    (k : ℕ) (hk : k ≤ n) :
    GlobalTheory.Hk3.IsLab V sp.w (List.replicate k 1 ++ List.replicate (n - k) 0) := by
  obtain ⟨x₀, -, e, f, ϖ', h1, h2, h3, h4, h5⟩ := exists_std hF Ps hs hn sp ϖ hϖ k hk
  exact GlobalTheory.SphLabelOps.isLab_of_divAt h1 h2 h3 (pairwise_lab _ _) h4 h5

theorem tSet_iff {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hs : GlobalTheory.NJoin.StdFrame hF Ps) (hn : V.rank = n) (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)) (hϖ : Formalism.AUTREP.IsUnif D.host.E sp.v ϖ)
    (k : ℕ) (hk : k ≤ n) (κ : Formalism.AUTREP.GAf D.host.E n) :
    κ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k ↔
      ∃ γ ∈ GlobalTheory.Hk3.rep V sp.w (List.replicate k 1 ++ List.replicate (n - k) 0),
        γ⁻¹ * Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w := by
  obtain ⟨x₀, hx₀, e, f, ϖ', h1, h2, h3, h4, h5⟩ := exists_std hF Ps hs hn sp ϖ hϖ k hk
  have hLab := GlobalTheory.SphLabelOps.isLab_of_divAt h1 h2 h3 (pairwise_lab _ _) h4 h5
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V sp.w
  have hR := GlobalTheory.SphLabelOps.reps_of_sphOp hK h1 h2 h3 h4 h5 (GlobalTheory.SphLabelOps.sphOp_rep hLab)
  have memK : ∀ l, l ∈ K ↔ l ∈ GlobalTheory.Hk3.hyp V sp.w := fun l => by rw [hK]; rfl
  have pre : ∀ l ∈ K, ∃ m, (m ∈ Umax D.host.E n ∧ TrivOutside {sp.v} m) ∧ Ps.ψ m = l := by
    intro l hl
    have hl' := (memK l).1 hl
    obtain ⟨m, rfl⟩ := Ps.onto l hl'.1.1
    exact ⟨m, (frame_hyp hF Ps hs sp m).1 hl', rfl⟩
  have img : ∀ m, (m ∈ Umax D.host.E n ∧ TrivOutside {sp.v} m) → Ps.ψ m ∈ K := fun m hm =>
    (memK _).2 ((frame_hyp hF Ps hs sp m).2 hm)
  constructor
  · intro hκ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (tSet_dc n sp ϖ k x₀ hx₀ κ).1 hκ
    obtain ⟨γ, ⟨hγ, hm⟩, -⟩ := hR.2 (Ps.ψ (k₁ * x₀ * k₂))
      ⟨Ps.ψ k₁, img _ hk₁, Ps.ψ k₂, img _ hk₂, by rw [map_mul, map_mul]⟩
    exact ⟨γ, hγ, (memK _).1 hm⟩
  · rintro ⟨γ, hγ, hm⟩
    obtain ⟨l₁, hl₁, l₂, hl₂, hγe⟩ := hR.1 γ hγ
    have hl : γ⁻¹ * Ps.ψ κ ∈ K := (memK _).2 hm
    obtain ⟨m₁, hm₁, e₁⟩ := pre l₁ hl₁
    obtain ⟨m₂, hm₂, e₂⟩ := pre (l₂ * (γ⁻¹ * Ps.ψ κ)) (mul_mem hl₂ hl)
    refine (tSet_dc n sp ϖ k x₀ hx₀ κ).2 ⟨m₁, hm₁, m₂, hm₂, Ps.inj ?_⟩
    rw [map_mul, map_mul, e₁, e₂, ← mul_assoc, ← mul_assoc, ← hγe, mul_inv_cancel, one_mul]

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

open Classical in

theorem finsum_cosets {G W ι : Type} [Group G] [AddCommGroup W] (J : Subgroup G) (T : Set G) (R : Finset ι)
    (x : ι → G) (F : G → W) (h1 : ∀ γ ∈ R, x γ ∈ T) (h2 : ∀ y ∈ T, ∃ γ ∈ R, (x γ)⁻¹ * y ∈ J)
    (h3 : ∀ γ ∈ R, ∀ γ' ∈ R, (x γ)⁻¹ * x γ' ∈ J → γ = γ')
    (hF : ∀ y ∈ T, ∀ y' ∈ T, y⁻¹ * y' ∈ J → ∀ g, F (g * y') = F (g * y)) (g : G) :
    (∑ᶠ c : G ⧸ J, if hc : ∃ y ∈ T, (y : G ⧸ J) = c then F (g * hc.choose) else 0) =
      ∑ γ ∈ R, F (g * x γ) := by
  classical
  have hsupp : (Function.support fun c : G ⧸ J =>
      if hc : ∃ y ∈ T, (y : G ⧸ J) = c then F (g * hc.choose) else 0) ⊆
      ↑(R.image fun γ => (x γ : G ⧸ J)) := by
    intro c hc
    by_cases h : ∃ y ∈ T, (y : G ⧸ J) = c
    · obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨γ, hγ, hm⟩ := h2 y hy
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 hm⟩)
    · exact absurd (by simp [h]) hc
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ y ∈ T, (y : G ⧸ J) = (x γ : G ⧸ J) := ⟨x γ, h1 γ hγ, rfl⟩
    rw [dif_pos hc]
    obtain ⟨hy, he⟩ := hc.choose_spec
    exact (hF _ hy _ (h1 γ hγ) (QuotientGroup.eq.1 he) g).symm
  · intro γ hγ γ' hγ' e
    exact h3 γ hγ γ' hγ' (QuotientGroup.eq.1 e)

theorem triv_mul {D : D7} {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))}
    {x y : Formalism.AUTREP.GAf D.host.E n} (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) :=
  fun v hv => by
    have e : (x * y).1.1 = x.1.1 * y.1.1 := rfl
    show (x * y).1.1.map (compAt D.host.E v) = 1
    rw [e, Matrix.map_mul]
    rw [show x.1.1.map (compAt D.host.E v) = 1 from hx v hv, show y.1.1.map (compAt D.host.E v) = 1 from hy v hv, mul_one]

theorem triv_inv {D : D7} {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))}
    {x : Formalism.AUTREP.GAf D.host.E n} (hx : TrivOutside T x) : TrivOutside T x⁻¹ := fun v hv => by
  have e : (x⁻¹).1.1.map (compAt D.host.E v) * x.1.1.map (compAt D.host.E v) = 1 := by
    rw [← Matrix.map_mul]
    have : (x⁻¹).1.1 * x.1.1 = 1 := by
      show (x⁻¹ * x).1.1 = 1
      rw [inv_mul_cancel]
      rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  show (x⁻¹).1.1.map (compAt D.host.E v) = 1
  rwa [show x.1.1.map (compAt D.host.E v) = 1 from hx v hv, mul_one] at e

theorem rep_inj {D : D7} (V : TH.HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (hd : GlobalTheory.Hk3.IsLab V P d) : ∀ γ ∈ GlobalTheory.Hk3.rep V P d, ∀ γ' ∈ GlobalTheory.Hk3.rep V P d,
      γ⁻¹ * γ' ∈ GlobalTheory.Hk3.hyp V P → γ = γ' := by
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨g₀, -, hR⟩ := GlobalTheory.SphLabelOps.exists_reps hK (GlobalTheory.SphLabelOps.sphOp_rep hd)
  intro γ hγ γ' hγ' hm
  rw [hK] at hm
  exact (hR.2 γ' (hR.1 γ' hγ')).unique ⟨hγ, hm⟩ ⟨hγ', by rw [inv_mul_cancel]; exact one_mem K⟩

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem sum_single {M : Type} [AddCommGroup M] [Module ℂ M] (d : List ℤ) (G : List ℤ → M) :
    ∑ d' ∈ (Finsupp.single d (1 : ℂ)).support, (Finsupp.single d (1 : ℂ)) d' • G d' = G d := by
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem eig_sum {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m)
    (f : D.what₂.Mt μ (j.1 + 1)) (y) (hy : X.R.extV j (X.tupT μ) y = X.fn hμ j f) (h)
    (hOps : GlobalTheory.Hk3.IsOpsV X.R j (X.tupT μ) h) (s : GlobalTheory.DownLift.Sys D)
    (hEig : GlobalTheory.DownLift.IsEigV X.R j (X.tupT μ) h s y) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hG : GlobalTheory.Hk3.Good X.R (X.tupT μ) P) (d : List ℤ) (hd : GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) P d)
    (g : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j)) :
    ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, X.fn hμ j f (g * a) = s P d • X.fn hμ j f g := by
  have hc : (X.R.cV j).Is := X.given.core.models.cV j
  have e1 := hOps P hG (Finsupp.single d 1) y
  have e2 := hEig P d hG hd
  have e4 : GlobalTheory.Hk3.hkF (Formalism.IndefR.Links.Vc D j) P (Finsupp.single d 1) ((X.R.HV j (X.tupT μ)).e y) =
      s P d • (X.R.HV j (X.tupT μ)).e y :=
    e1.symm.trans ((congrArg (X.R.HV j (X.tupT μ)).e e2).trans (map_smul _ _ _))
  have e3 := ((congrArg (fun F => (X.R.cV j).ext F g) e4).symm.trans
    (GlobalTheory.DefLiftHecke.ext_hkF (X.R.cV j) hc P (Finsupp.single d 1) ((X.R.HV j (X.tupT μ)).e y) g)).trans
    (sum_single d _)
  have hy2 : ∀ x, (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) x = X.fn hμ j f x := fun x =>
    (show X.R.extV j (X.tupT μ) y x = (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) x from rfl).symm.trans (congrFun hy x)
  calc ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, X.fn hμ j f (g * a)
      = ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) (g * a) :=
        Finset.sum_congr rfl fun a _ => (hy2 _).symm
    _ = (X.R.cV j).ext (s P d • (X.R.HV j (X.tupT μ)).e y) g := e3.symm
    _ = s P d • (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) g :=
        congrFun (map_smul (X.R.cV j).ext (s P d) ((X.R.HV j (X.tupT μ)).e y)) g
    _ = s P d • X.fn hμ j f g := by rw [hy2]

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem transport : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ sp : SplitPlace D.host.E, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i))) = s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := by
  intro _ hL D P X A _ _ _ i hμ j hj f y hy h hOps s hEig sp hG hJ ϖ hϖ k hk
  have hn : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hLab := isLab_std A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk
  have hsum := eig_sum X hμ j f y hy h hOps s hEig sp.w hG (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) hLab
  have hGf := GlobalTheory.DefLiftHecke.rep_mem_GfC (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)
  classical
  let xi : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j) → Formalism.AUTREP.GAf D.host.E D.R.nV := fun γ =>
    if hγ : γ ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j) then ((A.PV j).onto γ hγ).choose else 1
  have hxi : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (A.PV j).ψ (xi γ) = γ := fun γ hγ => by
    simp only [xi, dif_pos (hGf γ hγ)]
    exact ((A.PV j).onto γ (hGf γ hγ)).choose_spec
  have hT : ∀ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k, TrivOutside {sp.v} x := fun x hx => hx.1
  suffices key : ∀ (m : ℕ) (e : j.1 + 1 = m) (p1 : 1 ≤ m) (p2 : m ≤ D.R.m),
      (∀ κ : Formalism.AUTREP.GAf D.host.E D.R.nV, TrivOutside {sp.v} κ →
        (κ ∈ (P.M (D.nd.mu i) m p1 p2).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧
          ∀ hκ : κ ∈ (P.M (D.nd.mu i) m p1 p2).J, (P.M (D.nd.mu i) m p1 p2).χ ⟨κ, hκ⟩ = 1) →
      NG.heckeD (P.M (D.nd.mu i) m p1 p2).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k)
          ((P.M (D.nd.mu i) m p1 p2).real (e ▸ f)) =
        s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M (D.nd.mu i) m p1 p2).real (e ▸ f) from key _ hj _ _ hJ
  intro m e
  subst e
  intro p1 p2 hJ
  have hF : ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g =
      A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g))) := fun g => A.real (D.nd.mu i) hμ j f g
  have hinv : ∀ κ (hκ : κ ∈ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ ⟨κ, hκ⟩ = 1 →
      ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * κ) = (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g := by
    intro κ hκ h1 g
    have hmem : (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f ∈ Formalism.L2.NG.TypeSp (P.M (D.nd.mu i) (j.1 + 1) p1 p2).wt.ρ
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ := by
      rw [← (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real_range]
      exact LinearMap.mem_range_self _ _
    have := congrFun (hmem.2 ⟨κ, hκ⟩) g
    rw [h1] at this
    simp only [Units.val_one, one_smul] at this
    exact this
  have hmemT : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), xi γ ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k := by
    intro γ hγ
    refine (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk _).2 ⟨γ, hγ, ?_⟩
    rw [hxi γ hγ, inv_mul_cancel]
    exact GlobalTheory.DefLiftHecke.one_mem_hyp _ _
  funext g
  show (∑ᶠ c : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J,
      if hc : ∃ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k,
          (x : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J) = c then
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * hc.choose) else 0) = _
  rw [finsum_cosets (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J _ (GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)) xi _
    ?h1 ?h2 ?h3 ?h4 g]
  case h1 => exact hmemT
  case h2 =>
    intro x hx
    obtain ⟨γ, hγ, hm⟩ := (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk x).1 hx
    refine ⟨γ, hγ, ?_⟩
    rw [← hxi γ hγ, ← map_inv, ← map_mul] at hm
    obtain ⟨hU, hT'⟩ := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).1 hm
    exact (hJ _ hT').1.2 hU
  case h3 =>
    intro γ hγ γ' hγ' hm
    have ht := triv_mul (triv_inv (hT _ (hmemT γ hγ))) (hT _ (hmemT γ' hγ'))
    have hU := (hJ _ ht).1.1 hm
    have hh := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).2 ⟨hU, ht⟩
    rw [map_mul, map_inv, hxi γ hγ, hxi γ' hγ'] at hh
    exact rep_inj _ _ _ hLab γ hγ γ' hγ' hh
  case h4 =>
    intro y hy y' hy' hm g0
    have ht := triv_mul (triv_inv (hT _ hy)) (hT _ hy')
    have := hinv _ hm ((hJ _ ht).2 hm) (g0 * y)
    rw [mul_assoc, mul_inv_cancel_left] at this
    exact this
  rw [Pi.smul_apply, hF g]
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * xi γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) :=
        Finset.sum_congr rfl fun γ hγ => by rw [hF, ← mul_assoc, map_mul, hxi γ hγ]
    _ = A.eW _ hμ j (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) := (map_sum _ _ _).symm
    _ = _ := by rw [hsum, map_smul]

end GlobalTheory.EigTransport
