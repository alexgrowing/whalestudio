import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTripleLoc
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (IsInertAt)

namespace PT

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

local instance charZeroFv (v : Pl F) : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective

local instance invTwoFv (v : Pl F) : Invertible (2 : Fv F v) := invertibleOfNonzero two_ne_zero

local instance modTopEv (v : Pl F) : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩

section Pair

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W} {v : Pl F}
  {ψv : AddChar (Fv F v) ℂ} {dv : Darboux (symp (R := Fv F v) (cV σ v) (-1) (locM X.J v) (locM W.J v)) (Fin n × Fin d)}
  {χXv χWv : (Ev E v)ˣ →* Circle} {omv : UG (cV σ v) (locM X.J v) × UG (cV σ v) (locM W.J v) →* Module.End ℂ (Fn F n d v)}
  (L : IsLocPair M ψ χX χW om v ψv dv χXv χWv omv)
include L

theorem actsW {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) {hv : UG (cV σ v) (locM W.J v)}
    (e : (mat h).map (compFin F E v) = hv.1.1) {φ} (hφ : φ ∈ SB _) (φ₁) :
    Acts (evFin F v) (om (1, h)) φ φ₁ ↔ φ₁ = omv.comp (MonoidHom.inr _ _) hv φ := by
  obtain ⟨g', h', e1, e2, H⟩ := L.loc 1 (one_mem_UAt X v) h hh
  obtain rfl : g' = 1 := Subtype.ext (Units.ext (e1.symm.trans (Matrix.map_one _ (map_zero _) (map_one _))))
  obtain rfl : h' = hv := Subtype.ext (Units.ext (e2.symm.trans e))
  exact H φ hφ φ₁

theorem actsX {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) {gv : UG (cV σ v) (locM X.J v)}
    (e : (mat g).map (compFin F E v) = gv.1.1) {φ} (hφ : φ ∈ SB _) (φ₁) :
    Acts (evFin F v) (om (g, 1)) φ φ₁ ↔ φ₁ = omv.comp (MonoidHom.inl _ _) gv φ := by
  obtain ⟨g', h', e1, e2, H⟩ := L.loc g hg 1 (one_mem_UAt W v)
  obtain rfl : h' = 1 := Subtype.ext (Units.ext (e2.symm.trans (Matrix.map_one _ (map_zero _) (map_one _))))
  obtain rfl : g' = gv := Subtype.ext (Units.ext (e1.symm.trans e))
  exact H φ hφ φ₁

theorem exW {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    ∃ hv : UG (cV σ v) (locM W.J v), (mat h).map (compFin F E v) = hv.1.1 := by
  obtain ⟨-, h', -, e2, -⟩ := L.loc 1 (one_mem_UAt X v) h hh
  exact ⟨h', e2⟩

theorem splA : IsSplitting (sbClass (Fv F v)) ψv dv (fun (g : UG (cV σ v) (locM X.J v)) x => g.1.1 * x)
    (omv.comp (MonoidHom.inl _ _)) := by
  obtain ⟨-, d', h2, hA, -⟩ := L.weil
  have r : ∀ w, dv.rho ψv w = d'.rho ψv wᵀ := fun w => by rw [Darboux.rho, Darboux.rho, h2]
  refine ⟨hA.pres, fun g w φ hφ => ?_, hA.adm⟩
  rw [r, hA.impl _ _ _ hφ, r, actB, Matrix.transpose_mul]

theorem augAt_eq : augAt om v =
    Submodule.span ℂ {z | ∃ g, ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), z = omv.comp (MonoidHom.inl _ _) g φ₀ - φ₀} := by
  refine congrArg _ (Set.ext fun z => ⟨?_, ?_⟩)
  · rintro ⟨g, hg, φ, hφ, φ₁, -, ha, rfl⟩
    obtain ⟨g', -, e1, -, -⟩ := L.loc g hg 1 (one_mem_UAt W v)
    exact ⟨g', φ, hφ, by rw [(actsX L hg e1 hφ _).1 ha]⟩
  · rintro ⟨g', φ, hφ, rfl⟩
    obtain ⟨g, hg, e⟩ := L.surjX g'
    exact ⟨g, hg, φ, hφ, _, (splA L).pres g' φ hφ, (actsX L hg e hφ _).2 rfl, rfl⟩

theorem isEv_of {m : ℕ} {Cy : Matrix (Fin d) (Fin m) (AE F E)} (hC : At (evFin F v) Cy) {l : Fn F n d v →ₗ[ℂ] ℂ}
    (hl : IsEvAt M ψ v Cy l) (h0 : ∃ φ ∈ SB _, l φ ≠ 0) : IsEv (cV σ v) ψv dv (Cy.map (compFin F E v)) l := by
  refine ⟨h0, fun z φ hφ => ?_⟩
  have e : (z.map (ThKH.Iwas.sgE E v) * Cyᵀ).map (compFin F E v) = z * (Cy.map (compFin F E v))ᵀ := by
    rw [Matrix.map_mul, Matrix.transpose_map]
    congr 1
    exact Matrix.ext fun i j => ThKH.Iwas.comp_sgE _
  rw [← e]
  exact hl _ φ hφ _ (L.Heisenberg₂ _ (ThKH.Iwas.at_mul_right _ (ThKH.Iwas.at_transpose hC)) φ hφ)

theorem sec_eq_zero_iff (l : Fn F n d v →ₗ[ℂ] ℂ) {φ} (hφ : φ ∈ SB _) : secOf (omv.comp (MonoidHom.inr _ _)) l φ = 0 ↔
    ∀ h ∈ UAt σ W (evFin F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ → l φ₁ = 0 := by
  refine ⟨fun H h hh φ₁ ha => ?_, fun H => funext fun hv => ?_⟩
  · obtain ⟨hv, e⟩ := exW L hh
    rw [(actsW L hh e hφ _).1 ha]
    exact congrFun H hv
  · obtain ⟨h, hh, e⟩ := L.surjW hv
    exact H h hh _ ((actsW L hh e hφ _).2 rfl)

theorem isSplitPair (h2 : SiegelTransport) (h3 : LinearAct) {B : Base F E} (hσ : IsCMExt F E σ) {w} (hw : IsInertAt F E v w)
    {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hc : Continuous ψv) (h1 : ψv ≠ 1)
    (hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n) (hone : χWv = 1) {m : ℕ}
    {Cy : Matrix (Fin d) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) {l : Fn F n d v →ₗ[ℂ] ℂ} (hl : IsEvAt M ψ v Cy l)
    (h0 : ∃ φ ∈ SB _, l φ ≠ 0) : IsSplitPair (cV σ v) ψv (locM X.J v) (locM W.J v) dv χXv (Cy.map (compFin F E v))
      (omv.comp (MonoidHom.inl _ _)) (omv.comp (MonoidHom.inr _ _)) l := by
  subst hone
  have a1 := isHerm_loc (v := v) hX
  have a2 := isSkew_loc (v := v) hW
  have a3 := isLagr_loc hσ hw hW hL
  have a4 := isEv_of L hL.supp hl h0
  exact ⟨a1, a2, a3, (Fintype.card_fin n).symm ▸ resEtaPow_loc hσ.2.2.1 hres L.chX, L.weil.1.1,
    h2 _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) hc h1 _ _ _ _ _ _ dv _ _ _ a1 a2 a3 L.weil.1, splA L, a4,
    h3 _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) hc h1 _ _ _ _ _ _ dv _ _ _ l a1 a2 a3 L.weil a4⟩

end Pair

theorem secOf_om {G S : Type} [Group G] [AddCommGroup S] [Module ℂ S] (om : G →* Module.End ℂ S) (l : S →ₗ[ℂ] ℂ) (h : G) (φ : S) :
    secOf om l (om h φ) = fun g => secOf om l φ (g * h) := funext fun g => by
  change l (om g (om h φ)) = l (om (g * h) φ)
  rw [map_mul, Module.End.mul_apply]

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {v : Pl F}
  {w : HeightOneSpectrum (𝓞 E)}

theorem exists_loc (h1 : LocPairEx) (hT : IsTriple B G X om om') (hw : IsInertAt F E v w) (hv : v ∉ X.T) :
    ∃ ψv χ dv omv dv' omv', IsLocPair G.M B.ψ X.β (X.β / X.α) om v ψv dv χ 1 omv ∧
      IsLocPair G.M' B.ψ X.α (X.α / X.β) om' v ψv dv' χ 1 omv' ∧ Continuous ψv ∧ ψv ≠ 1 ∧ Continuous χ := by
  have P : PairOK B G.V G.W G.M om := ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩
  have P' : PairOK B G.V' G.W G.M' om' := ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩
  obtain ⟨ψv, dv, χ, χ₁, omv, L⟩ := h1 F E σ _ _ B _ _ _ _ _ _ P hT.weil v
  obtain ⟨ψv', dv', χ', χ₁', omv', L'⟩ := h1 F E σ _ _ B _ _ _ _ _ _ P' hT.weil' v
  obtain rfl : ψv' = ψv := AddChar.ext _ _ fun x => (L'.psi x).trans (L.psi x).symm
  have hab : w ∉ above E (X.T : Set (Pl F)) := fun h => hv (under_eq_of_isInertAt hw ▸ h)
  have uα := hT.chars.unrα w hab
  have uβ := hT.chars.unrβ w hab
  have hres : ∀ t, X.β (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) t) =
      X.α (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) t) := fun t => Circle.ext (by
    rw [hT.chars.resα t, hT.chars.resβ t, neg_one_pow_congr (Nat.even_add.1 hT.geo.even)])
  have k1 : ∀ {μ}, IsLocChar (X.β / X.α) v μ → μ = 1 := fun H =>
    loc_eq_one hw (div_eq_mul_inv X.β X.α ▸ uβ.mul uα.inv) (fun t => by rw [MonoidHom.div_apply, hres, div_self']) H
  have k2 : ∀ {μ}, IsLocChar (X.α / X.β) v μ → μ = 1 := fun H =>
    loc_eq_one hw (div_eq_mul_inv X.α X.β ▸ uα.mul uβ.inv) (fun t => by rw [MonoidHom.div_apply, hres, div_self']) H
  obtain rfl := k1 L.chW
  obtain rfl := k2 L'.chW
  obtain rfl : χ = χ' := div_eq_one.1 (k1 fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, L.chX z hz, L'.chX z hz])
  obtain ⟨c1, c2⟩ := psi_good hT.base.std (hT.base.inert v w hw).2.2 L.psi
  exact ⟨_, _, dv, omv, dv', omv', L, L', c1, c2, continuous_loc hw hT.chars.heckeβ.1 L.chX⟩

theorem coinvEmbeds_of (p1 : CoinvHyp) (h1 : LocPairEx) (h2 : SiegelTransport) (h3 : LinearAct) : CoinvEmbeds := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv m Cy hL
  obtain ⟨ψv, χ, dv, omv, dv', omv', L, L', c1, c2, c3⟩ := exists_loc h1 hT hw hv
  have hσ := hT.base.cm
  refine ⟨fun l hl h0 φ hφ => ?_, fun l hl h0 φ hφ => ?_⟩
  · rw [augAt_eq L, ← sec_eq_zero_iff L l hφ]
    exact p1 _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ _ l c3
      (isSplitPair L h2 h3 hσ hw hT.geo.hV hT.geo.hW c1 c2 hT.chars.resβ rfl hL hl h0) φ hφ
  · rw [augAt_eq L', ← sec_eq_zero_iff L' l hφ]
    exact p1 _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv' _ _ _ _ l c3
      (isSplitPair L' h2 h3 hσ hw hT.geo.hV' hT.geo.hW c1 c2 hT.chars.resα rfl hL hl h0) φ hφ

theorem compAtTriple_of (p1 : CoinvHyp) (p2 : KudlaSweetTheorem) (h1 : LocPairEx) (h2 : SiegelTransport) (h3 : LinearAct)
    (hB : Iwasawa) (hC : EvVac) : CompAtTriple := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv
  have P : PairOK B G.V G.W G.M om := ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩
  have P' : PairOK B G.V' G.W G.M' om' := ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩
  obtain ⟨m, Cy, hL, hAd, -⟩ := hB F E σ _ _ B _ _ _ _ P v hT.geo.even ⟨w, hw⟩
  obtain ⟨l, hl, hl0⟩ := hC F E σ _ _ B _ _ _ _ P v ⟨w, hw⟩ m Cy hL hAd
  obtain ⟨l', hl', hl0'⟩ := hC F E σ _ _ B _ _ _ _ P' v ⟨w, hw⟩ m Cy hL hAd
  have hs := (hT.geo.hM.vac v).1
  have hs' := (hT.geo.hM'.vac v).1
  obtain ⟨ψv, χ, dv, omv, dv', omv', L, L', c1, c2, c3⟩ := exists_loc h1 hT hw hv
  have hσ := hT.base.cm
  have S := isSplitPair L h2 h3 hσ hw hT.geo.hV hT.geo.hW c1 c2 hT.chars.resβ rfl hL hl ⟨_, hs, hl0⟩
  have S' := isSplitPair L' h2 h3 hσ hw hT.geo.hV' hT.geo.hW c1 c2 hT.chars.resα rfl hL hl' ⟨_, hs', hl0'⟩
  have C := p1 _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ _ l c3 S
  have C' := p1 _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv' _ _ _ _ l' c3 S'
  rw [← augAt_eq L] at C
  rw [← augAt_eq L'] at C'
  have r1 := hL.rank
  have r2 := hT.geo.lt
  have r3 := hT.geo.aBig
  obtain ⟨hirr, T, hT1, hT2⟩ := p2 _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ _ _ _ dv dv' _ _ _ _ l _ _ l' c3
    (by omega) (by omega) r1 (isAbove_of_hasAnti r2.le hT.geo.even (hasAnti_loc hσ hw hT.geo.hV) (hasAnti_loc hσ hw hT.geo.hV'))
    S S'
  set s := secOf (omv.comp (MonoidHom.inr _ _)) l with hsec
  set s' := secOf (omv'.comp (MonoidHom.inr _ _)) l' with hsec'
  obtain ⟨j, hj⟩ := exists_to_quot s' (augAt om' v) (SB _) fun φ hφ => (C' φ hφ).2
  have up : ∀ φ ∈ SB _, ∃ φ' ∈ SB _, s' φ' = T (s φ) := fun φ hφ =>
    (hT1 ▸ Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hφ) : T (s φ) ∈ (SB _).map s')
  refine ⟨fun h => hl0' ?_, fun N hN1 hN2 hN3 => ?_, j ∘ₗ T ∘ₗ s, le_antisymm ?_ ?_, fun φ hφ => ?_,
    fun h hh φ hφ φ' hφ' φ₁ _ φ₁' _ b1 b2 e => ?_⟩
  · have := congrFun ((C' _ hs').1 (h ▸ hs')) 1
    rwa [show s' (G.M'.vac v) 1 = l' (omv'.comp (MonoidHom.inr _ _) 1 (G.M'.vac v)) from rfl, map_one] at this
  · refine (hirr (N.map s') (Submodule.map_mono hN2) ?_).imp (fun h => le_antisymm (fun φ hφ => ?_) hN1)
      fun h => le_antisymm hN2 fun φ hφ => ?_
    · rintro _ ⟨φ, hφ, rfl⟩ hv
      obtain ⟨h, hh, e⟩ := L'.surjW hv
      exact ⟨_, hN3 h hh φ hφ _ (S'.splB.pres hv φ (hN2 hφ)) ((actsW L' hh e (hN2 hφ) _).2 rfl), secOf_om _ _ _ _⟩
    · exact (C' φ (hN2 hφ)).2 ((Submodule.mem_bot ℂ).1 (h ▸ Submodule.mem_map_of_mem hφ))
    · obtain ⟨φ₀, h₀, e⟩ : s' φ ∈ N.map s' := h ▸ Submodule.mem_map_of_mem hφ
      have := hN1 ((C' _ (sub_mem hφ (hN2 h₀))).2 (by rw [map_sub, e, sub_self]))
      simpa using add_mem this h₀
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨φ', hφ', e⟩ := up φ hφ
    exact ⟨φ', hφ', (hj φ' hφ').symm.trans (congrArg j e)⟩
  · rintro _ ⟨φ', hφ', rfl⟩
    obtain ⟨_, ⟨φ, hφ, rfl⟩, e⟩ : s' φ' ∈ ((SB _).map s).map T := hT1 ▸ Submodule.mem_map_of_mem hφ'
    exact ⟨φ, hφ, (congrArg j e).trans (hj φ' hφ')⟩
  · change j (T (s φ)) = 0
    rw [(C φ (augAt_le om v hφ)).1 hφ, map_zero, map_zero]
  · obtain ⟨hv, eh⟩ := exW L hh
    obtain ⟨φ₀, h₀, e₀⟩ := up φ hφ
    have e1 : s' φ' = T (s φ) := by
      have : φ₀ - φ' ∈ augAt om' v := (Submodule.Quotient.eq _).1 (((hj φ₀ h₀).symm.trans (congrArg j e₀)).trans e)
      have := (C' _ (sub_mem h₀ hφ')).1 this
      rw [map_sub, sub_eq_zero] at this
      exact this.symm.trans e₀
    rw [(actsW L hh eh hφ _).1 b1, (actsW L' hh eh hφ' _).1 b2, ← hj _ (S'.splB.pres hv φ' hφ')]
    change j (T (s _)) = j (s' _)
    rw [hsec, hsec', secOf_om, secOf_om, hT2 _ (Submodule.mem_map_of_mem hφ), ← hsec', e1]

end PT

theorem coinvariant_embedding_at_triple : HypothesesAtTriple := fun p1 p2 h1 h2 h3 hB hC =>
  ⟨PT.coinvEmbeds_of p1 h1 h2 h3, PT.compAtTriple_of p1 p2 h1 h2 h3 hB hC⟩

end PositivityTheory.ThK
