import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalDilatedClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal

noncomputable section

namespace GlobalTheory.LvT.StartTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

section Values

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ)

def valAt (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (d : S.D b) : Fr emb σ n → ℂ := S.trTo emb σ b d (φ (S.cl b d))

omit [StarRing E] [NumberField K] [StarRing K] in
theorem tr_mul (b : S.β) (g h : S.G b) (F : Fr emb σ n → ℂ) :
    S.tr emb σ b (g * h) F = S.tr emb σ b g (S.tr emb σ b h F) := by
  funext y
  simp only [GStep.tr, trFr_apply, map_mul, Units.val_mul, _root_.mul_inv_rev, frMul_mul, mul_assoc]

variable {S}

theorem valAt_eq (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (c : S.Cl) (g : S.G c.1) :
    valAt S emb σ φ c.1 (g • S.rep c) = S.tr emb σ c.1 g (φ c) := by
  obtain ⟨b, q⟩ := c
  have hq : (Quotient.mk _ (g • S.rp b q) : MulAction.orbitRel.Quotient (S.G b) (S.D b)) = q :=
    (Quotient.sound (show (MulAction.orbitRel (S.G b) (S.D b)).r (g • S.rp b q) (S.rp b q) from ⟨g, rfl⟩)).trans (S.rp_spec b q)
  have h1 : S.mv b (g • S.rp b q) • S.rp b (Quotient.mk _ (g • S.rp b q)) = g • S.rp b q := S.mv_smul b _
  rw [hq] at h1
  have h2 : S.mv b (g • S.rp b q) = g := by
    have := hf b (g⁻¹ * S.mv b (g • S.rp b q)) (S.rp b q) (by rw [mul_smul, h1, inv_smul_smul])
    exact (inv_mul_eq_one.1 this).symm
  show S.tr emb σ b (S.mv b (g • S.rp b q)) (φ ⟨b, Quotient.mk _ (g • S.rp b q)⟩) = _
  rw [h2, hq]

theorem valAt_rep (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (c : S.Cl) : valAt S emb σ φ c.1 (S.rep c) = φ c := by
  have := valAt_eq emb σ hf φ c 1
  rwa [one_smul, DiaStab.tr_one] at this

theorem valAt_smul (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (g : S.G b) (d : S.D b) :
    valAt S emb σ φ b (g • d) = S.tr emb σ b g (valAt S emb σ φ b d) := by
  have h := valAt_eq emb σ hf φ (S.cl b d) (g * S.mv b d)
  rw [mul_smul, S.mv_smul, tr_mul] at h
  exact h

variable {S' : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {A' : TDat S' ST} {T : ℕ}

theorem up_match (hf : S.Free) (hA : A.Ok T) (hT : A.Tied T) (hA' : A'.Ok T) (hT' : A'.Tied T) (P : ST)
    (s : ∀ c, Finset (A.lv P c)) (hs : ∀ c x, x ∈ s c ↔ A.fv P c x = 1)
    (c' : S'.Cl) (s' : Finset (A'.lv P c')) (hs' : ∀ x, x ∈ s' ↔ A'.fv P c' x = 1)
    (φ : S.Cl → Fr emb σ n → ℂ) (φ' : S'.Cl → Fr emb σ n → ℂ) (b : S.β) (d : S.D b)
    (hN : A.N b d = A'.N c'.1 (S'.rep c')) (hF : A.f b d P = A'.f c'.1 (S'.rep c') P)
    (hup : ∀ x ∈ A.N b d, A.f b d P x = 1 →
      valAt S' emb σ φ' c'.1 (A'.up c'.1 (S'.rep c') P x) = valAt S emb σ φ b (A.up b d P x)) :
    valAt S emb σ (fun c => ∑ x ∈ s c, valAt S emb σ φ c.1 (A.upPt P c x)) b d =
      ∑ x ∈ s', valAt S' emb σ φ' c'.1 (A'.upPt P c' x) := by
  have hmv := S.mv_smul b d
  obtain ⟨u, hu⟩ := DilFv.exists_act_equiv A hA b (S.mv b d) (S.rep (S.cl b d)) (A'.N c'.1 (S'.rep c'))
    (by rw [hmv]; exact hN)
  obtain ⟨e, he⟩ := DilFv.exists_red_equiv P.1.asIdeal u
  have hfv : ∀ x : A.N b (S.rep (S.cl b d)), A.f b d P (u x) = A.f b (S.rep (S.cl b d)) P x := fun x => by
    have := hA.f_act b (S.mv b d) (S.rep (S.cl b d)) P x
    rwa [hmv, ← hu] at this
  show S.tr emb σ b (S.mv b d) (∑ x ∈ s (S.cl b d), valAt S emb σ φ b (A.upPt P (S.cl b d) x)) = _
  rw [map_sum]
  refine Finset.sum_equiv e.toEquiv (fun x => ?_) fun x hx => ?_
  · rw [hs, hs']
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e1 := DilFv.fv_mk A hA P (S.cl b d) x
    have e2 := DilFv.fv_mk A' hA' P c' (u x)
    have e3 : A'.fv P c' (e.toEquiv (Submodule.Quotient.mk x)) = A'.fv P c' (Submodule.Quotient.mk (u x)) :=
      congrArg _ (he x)
    rw [e1, e3, e2, ← hF, hfv]
  · have hx0 : (Submodule.Quotient.mk (Quotient.out x) : A.lv P (S.cl b d)) = x := Quotient.out_eq x
    have h1 : A.f b (S.rep (S.cl b d)) P (Quotient.out x : A.N b (S.rep (S.cl b d))) = 1 := by
      rw [← (hs _ x).1 hx]
      conv_rhs => rw [← hx0]
      exact (DilFv.fv_mk A hA P (S.cl b d) _).symm
    have h2 := hT.up_act b (S.mv b d) (S.rep (S.cl b d)) P _ (Quotient.out x : A.N b (S.rep (S.cl b d))).2 h1
    rw [hmv, ← hu] at h2
    have h3 : (Submodule.Quotient.mk (Quotient.out (e.toEquiv x)) : A'.lv P c') =
        Submodule.Quotient.mk (u (Quotient.out x)) :=
      (Quotient.out_eq _).trans ((congrArg e hx0).symm.trans (he _))
    rw [Submodule.Quotient.eq] at h3
    have h4 := Submodule.mem_map_of_mem (f := (A'.N c'.1 (S'.rep c')).subtype) h3
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at h4
    have h5 := hT'.up_congr c'.1 (S'.rep c') P _ _ h4
    unfold TDat.upPt
    rw [← valAt_smul emb σ hf]
    refine Eq.trans ?_ (congrArg _ h5.symm)
    rw [hup _ (by rw [hN]; exact (u _).2) ((hfv _).trans h1), h2]

end Values

section Points

variable {X : Fields} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem exists_pt {y : Ys X n} (hy : ∀ N, y.ys N = {∅}) (d : DecoSet X.E n ST SG) :
    ∃ p : PtY ST SG Q y, p.1.1.deco = d := by
  choose f hf using fun P : Q => GlobalTheory.CharValCompare.exists_isFr P.1 d.2.lat
  exact ⟨⟨(⟨(d, f), hf⟩, ∅), by rw [hy]; rfl⟩, rfl⟩

theorem mv_deco {y : Ys X n} (p : PtY ST SG Q y) (d : DecoSet X.E n ST SG) (h : (p.mv d).1.1.deco.1.N = d.1.N) :
    (p.mv d).1.1.deco = d := by
  by_cases hc : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N
  · exact congrArg (fun q : PtY ST SG Q y => q.1.1.deco) (dif_pos hc : p.mv d = _)
  · have h1 : p.mv d = p := dif_neg hc
    rw [h1] at h
    refine absurd ⟨fun P x => ?_, h ▸ p.2⟩ hc
    have := p.1.1.2 P x
    unfold Deco.at at this ⊢
    rw [← h]
    exact this

variable {T : ℕ} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG}
  {Θ : β → LevQFam X.E X.K n Q} {pref : DecoF X.E n ST SG Q → Prop}

theorem up_deco (hT : (tdatY ST T y β Λ Θ pref).Tied T) (b : β) (p : PtY ST SG Q y) (P : ST) (x : Sp X.E n)
    (hx : x ∈ p.1.1.deco.1.N) (hf : p.1.1.deco.1.f P x = 1) :
    (p.mv (p.1.1.deco.up P (T : 𝓞 X.E) x)).1.1.deco = p.1.1.deco.up P (T : 𝓞 X.E) x := by
  by_cases hc : (p.1.1.deco.1.up P (T : 𝓞 X.E) x).Ok
  · apply mv_deco
    have h1 := congrArg Deco.N (hT.up_deco b p P x hx hf)
    refine Eq.trans h1 ?_
    unfold DecoSet.up
    rw [dif_pos hc]
    rfl
  · have h1 : p.1.1.deco.up P (T : 𝓞 X.E) x = p.1.1.deco := dif_neg hc
    rw [h1]
    exact congrArg (fun q : PtY ST SG Q y => q.1.1.deco) (dif_pos ⟨p.1.1.2, p.2⟩ : p.mv p.1.1.deco = _)

theorem dia_deco (p : PtY ST SG Q y) (P : ST) (a : (Res P.1)ˣ) :
    (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.deco = DecoSet.dia1 P a p.1.1.deco :=
  congrArg (fun q : PtY ST SG Q y => q.1.1.deco)
    (dif_pos ⟨p.1.1.2, p.2⟩ : p.mv (DecoSet.dia1 P a p.1.1.deco) = _)

theorem exists_lift {y' : Ys X n} (hy : ∀ N, y.ys N = {∅}) {Λ₁ Λ₂ : LevFam X.E X.K n SG} {Θ₁ : LevQFam X.E X.K n Q}
    {Θ₂ : LevQFam X.E X.K n Q'} (hΛ : Λ₁ = Λ₂) (h₁ : Θ₁ = LevQFam.top X.E X.K n Q) (h₂ : Θ₂ = LevQFam.top X.E X.K n Q')
    (g' : FrmG Λ₂ Θ₂) (p₀ p : PtY ST SG Q y) (p' : PtY ST SG Q' y') (h0 : p₀.1.1.deco = p'.1.1.deco)
    (h1 : p.1.1.deco = (FrmG.incl Λ₂ Θ₂ g' • p'.1.1).deco) :
    ∃ g : FrmG Λ₁ Θ₁, (ptYAct y Λ₁ Θ₁).smul g p₀ = p ∧ g.1 = g'.1 ∧
      Λ₁.chr g.2.1 * Θ₁.chr g.2.2 = Λ₂.chr g'.2.1 * Θ₂.chr g'.2.2 := by
  subst hΛ h₁ h₂
  have hd : p.1.1.deco = ((g'.1, (g'.2.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • p₀.1.1.deco := by
    rw [h0]; exact h1
  have hc : ∀ P : Q, (p.1.1.fr P)⁻¹ * g'.1.1 * p₀.1.1.fr P ∈ GLint X.E n P.1 := fun P x => by
    have a1 := p.1.1.2 P ((p.1.1.fr P).symm (g'.1.1 (p₀.1.1.fr P x)))
    have a2 := p₀.1.1.2 P x
    refine a1.symm.trans (Iff.trans ?_ a2)
    show p.1.1.fr P ((p.1.1.fr P).symm (g'.1.1 (p₀.1.1.fr P x))) ∈ p.1.1.deco.1.at P.1 ↔ _
    rw [LinearEquiv.apply_symm_apply, hd]
    show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.gmap g'.1.1 p₀.1.1.deco.1.N) ↔ _
    rw [mem_localization_gmap, LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨(g'.1, g'.2.1, ⟨fun P => ⟨_, hc P⟩, fun P _ => Subgroup.mem_top _⟩), ?_, rfl, ?_⟩
  · refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hd.symm ?_)) ?_)
    · funext P
      show g'.1.1 * p₀.1.1.fr P * ((p.1.1.fr P)⁻¹ * g'.1.1 * p₀.1.1.fr P)⁻¹ = p.1.1.fr P
      group
    · have a1 := p.2
      have a2 := ((ptYAct y Λ₁ (LevQFam.top X.E X.K n Q)).smul
        (g'.1, g'.2.1, ⟨fun P => ⟨_, hc P⟩, fun P _ => Subgroup.mem_top _⟩) p₀).2
      rw [hy] at a1 a2
      exact a2.trans a1.symm
  · rw [LevQFam.top_chr, LevQFam.top_chr]

end Points

section Start

variable {X : Fields} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))} {T : ℕ}
  {y y' : Ys X n} {β β' : Type} {iβ : Fintype β} {jβ : DecidableEq β} {iβ' : Fintype β'} {jβ' : DecidableEq β'}
  {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q} {pref : DecoF X.E n ST SG Q → Prop}
  {Λ' : β' → LevFam X.E X.K n SG} {Θ' : β' → LevQFam X.E X.K n Q'} {pref' : DecoF X.E n ST SG Q' → Prop}
  (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n)

def ForgetsFrames (e : ((stepY ST y β Λ Θ pref).Cl → Fr X.emb σ n → ℂ) ≃ₗ[ℂ]
    ((stepY ST y' β' Λ' Θ' pref').Cl → Fr X.emb σ n → ℂ)) : Prop :=
  ∀ φ ∈ (stepY ST y β Λ Θ pref).Fi X.emb σ lam, ∀ (b : β) (b' : β') (p : PtY ST SG Q y) (p' : PtY ST SG Q' y'),
    p.1.1.deco = p'.1.1.deco →
      valAt (stepY ST y' β' Λ' Θ' pref') X.emb σ (e φ) b' p' = valAt (stepY ST y β Λ Θ pref) X.emb σ φ b p

theorem exists_read (hy : ∀ N, y.ys N = {∅}) (b₀ : β) (hb : ∀ b, b = b₀) {Λ₀ : LevFam X.E X.K n SG} (hΛ : ∀ b, Λ b = Λ₀)
    (hΛ' : ∀ b, Λ' b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (hΘ' : ∀ b, Θ' b = LevQFam.top X.E X.K n Q')
    (hf : (stepY ST y β Λ Θ pref).Free) :
    ∃ e : ((stepY ST y β Λ Θ pref).Cl → Fr X.emb σ n → ℂ) →ₗ[ℂ] ((stepY ST y' β' Λ' Θ' pref').Cl → Fr X.emb σ n → ℂ),
      ∀ φ (b : β) (b' : β') (p : PtY ST SG Q y) (p' : PtY ST SG Q' y'), p.1.1.deco = p'.1.1.deco →
        valAt (stepY ST y' β' Λ' Θ' pref') X.emb σ (e φ) b' p' = valAt (stepY ST y β Λ Θ pref) X.emb σ φ b p := by
  choose π hπ using fun c : (stepY ST y' β' Λ' Θ' pref').Cl =>
    exists_pt (Q := Q) hy (show PtY ST SG Q' y' from (stepY ST y' β' Λ' Θ' pref').rep c).1.1.deco
  refine ⟨LinearMap.pi fun c => ((stepY ST y β Λ Θ pref).trTo X.emb σ b₀ (π c)).toLinearMap ∘ₗ
    LinearMap.proj ((stepY ST y β Λ Θ pref).cl b₀ (π c)), fun φ b b' p p' h => ?_⟩
  obtain rfl := hb b
  have hm := (stepY ST y' β' Λ' Θ' pref').mv_smul b' p'
  obtain ⟨g, g1, g2, g3⟩ := exists_lift hy ((hΛ b).trans (hΛ' b').symm) (hΘ b) (hΘ' b')
    ((stepY ST y' β' Λ' Θ' pref').mv b' p') (π ((stepY ST y' β' Λ' Θ' pref').cl b' p')) p _ (hπ _)
    (h.trans (congrArg (fun q : PtY ST SG Q' y' => q.1.1.deco) hm).symm)
  have h1 := valAt_smul X.emb σ hf φ b g (π ((stepY ST y' β' Λ' Θ' pref').cl b' p'))
  refine Eq.trans ?_ (h1.symm.trans (congrArg _ g1))
  have h2 : (stepY ST y' β' Λ' Θ' pref').tr X.emb σ b' ((stepY ST y' β' Λ' Θ' pref').mv b' p') =
      (stepY ST y β Λ Θ pref).tr X.emb σ b g :=
    congrArg₂ (trFr X.emb σ) (congrArg (ufGL X.E n) g2.symm) g3.symm
  exact congrFun (congrArg DFunLike.coe h2) _

variable {σ lam} {e : ((stepY ST y β Λ Θ pref).Cl → Fr X.emb σ n → ℂ) ≃ₗ[ℂ]
    ((stepY ST y' β' Λ' Θ' pref').Cl → Fr X.emb σ n → ℂ)}

theorem up_mem (hf : (stepY ST y β Λ Θ pref).Free) (P : ST) (s : ∀ c, Finset ((tdatY ST T y β Λ Θ pref).lv P c))
    {φ} (hφ : φ ∈ (stepY ST y β Λ Θ pref).Fi X.emb σ lam) :
    (fun c => ∑ x ∈ s c, valAt (stepY ST y β Λ Θ pref) X.emb σ φ c.1 ((tdatY ST T y β Λ Θ pref).upPt P c x)) ∈
      (stepY ST y β Λ Θ pref).Fi X.emb σ lam :=
  DiaStab.mem_Fi _ X.emb σ lam hf _ fun _ => Submodule.sum_mem _ fun _ _ => DiaStab.tr_mem _ X.emb σ _ _ _ (hφ _).1

theorem ForgetsFrames.up (he : ForgetsFrames σ lam e) (hy : ∀ N, y.ys N = {∅}) (b₀ : β)
    (hf : (stepY ST y β Λ Θ pref).Free) (hf' : (stepY ST y' β' Λ' Θ' pref').Free)
    (hA : (tdatY ST T y β Λ Θ pref).Ok T) (hT : (tdatY ST T y β Λ Θ pref).Tied T)
    (hA' : (tdatY ST T y' β' Λ' Θ' pref').Ok T) (hT' : (tdatY ST T y' β' Λ' Θ' pref').Tied T) (P : ST)
    (s : ∀ c, Finset ((tdatY ST T y β Λ Θ pref).lv P c)) (hs : ∀ c x, x ∈ s c ↔ (tdatY ST T y β Λ Θ pref).fv P c x = 1)
    (s' : ∀ c, Finset ((tdatY ST T y' β' Λ' Θ' pref').lv P c))
    (hs' : ∀ c x, x ∈ s' c ↔ (tdatY ST T y' β' Λ' Θ' pref').fv P c x = 1)
    {φ} (hφ : φ ∈ (stepY ST y β Λ Θ pref).Fi X.emb σ lam) :
    e (fun c => ∑ x ∈ s c, valAt (stepY ST y β Λ Θ pref) X.emb σ φ c.1 ((tdatY ST T y β Λ Θ pref).upPt P c x)) =
      fun c => ∑ x ∈ s' c,
        valAt (stepY ST y' β' Λ' Θ' pref') X.emb σ (e φ) c.1 ((tdatY ST T y' β' Λ' Θ' pref').upPt P c x) := by
  funext c
  obtain ⟨p, hp⟩ := exists_pt (Q := Q) hy (show PtY ST SG Q' y' from (stepY ST y' β' Λ' Θ' pref').rep c).1.1.deco
  refine (valAt_rep X.emb σ hf' _ c).symm.trans ((he _ (up_mem hf P s hφ) b₀ c.1 p _ hp).trans ?_)
  have hN := congrArg (fun d : DecoSet X.E n ST SG => d.1.N) hp
  have hF := congrArg (fun d : DecoSet X.E n ST SG => d.1.f P) hp
  refine up_match X.emb σ hf hA hT hA' hT' P s hs c (s' c) (hs' c) φ (e φ) b₀ p hN hF fun x hx h1 => ?_
  refine he φ hφ b₀ c.1 _ _ ?_
  exact (up_deco hT b₀ p P x hx h1).trans ((congrArg (fun d : DecoSet X.E n ST SG => d.up P (T : 𝓞 X.E) x) hp).trans
    (up_deco hT' c.1 _ P x (hN ▸ hx) ((congrFun hF x).symm.trans h1)).symm)

end Start

section Lattice

variable {D : D7} {u : D.what₂.Word} {X Y : Ch D u} {e : Fn X 0 ≃ₗ[ℂ] Fn Y 0} {eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0}

theorem nlam_map (w : D.what₂.places.Pl) (hT : Y.A.T = X.A.T) (hemb : ∀ x, Y.fm.emb 0 (eL x) = e (X.fm.emb 0 x))
    (hlat : ∀ x, x ∈ (X.fm.lat 0).L → eL x ∈ (Y.fm.lat 0).L)
    (hNm : ∀ v', ∃ v, ∀ φ ∈ X.fm.Fi 0, e (Nm X 0 v φ) = Nm Y 0 v' (e φ)) (hexp : expT Y w = expT X w)
    (hmem : ∀ φ ∈ X.fm.Fi 0, Uprod X 0 w φ ∈ X.fm.Fi 0)
    (hU : ∀ φ ∈ X.fm.Fi 0, e (Uprod X 0 w φ) = Uprod Y 0 w (e φ)) {x : Vl X 0} (hx : x ∈ Nlam X w) : eL x ∈ Nlam Y w := by
  have hS : ∀ z ∈ X.fm.S 0 w, eL z ∈ Y.fm.S 0 w := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span (hlat z hz)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Subring.smul_def, map_smul]
      exact Submodule.smul_mem _ r ha
  have hR : ∀ z ∈ X.fm.ramSub, eL z ∈ Y.fm.ramSub := fun z hz => by
    have hz' : X.fm.emb 0 z ∈ X.A.Mram := hz
    show Y.fm.emb 0 (eL z) ∈ Y.A.Mram
    rw [← MramI_zero] at hz' ⊢
    unfold MramI at hz' ⊢
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, emb_mem_Fi, true_and] at hz' ⊢
    intro v'
    obtain ⟨v, hv⟩ := hNm v'
    rw [hemb, ← hv _ (emb_mem_Fi X 0 z), hz' v, map_zero]
  have hP : ∀ (k : ℕ), ∀ φ ∈ X.fm.Fi 0, e ((Uprod X 0 w ^ k) φ) = (Uprod Y 0 w ^ k) (e φ) := fun k => by
    induction k with
    | zero => exact fun _ _ => rfl
    | succ k ih =>
      intro φ hφ
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← hU φ hφ]
      exact ih _ (hmem φ hφ)
  obtain ⟨z, hz, hh⟩ := hx
  refine ⟨eL z, ⟨hS z hz.1, hR z hz.2⟩, ?_⟩
  rw [hemb, hemb, hh, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hP _ _ (emb_mem_Fi X 0 z), hT, hexp]

end Lattice

section Chains

@[reducible] def fieldsOver (D : D7) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (emb : D.what₂.Tau → E →+* D.what₂.LL) : Fields where
  F := F
  E := E
  K := D.what₂.LL
  Tau := D.what₂.Tau
  deTau := Classical.decEq _
  emb := emb

@[reducible] def chOf (D : D7) (u : D.what₂.Word) {E : Type} [Field E] [NumberField E] [StarRing E]
    (emb : D.what₂.Tau → E →+* D.what₂.LL) {I : ChainIn E D.what₂.LL D.what₂.Tau D.R} {J : AtIn I} {Q : PerIn I}
    (Z : FmIn J D.what₂.places) (hI : I.Ok) (hJ : J.Ok) (hQ : Q.Ok) (l : J.Laws emb D.what₂.embLL (D.hcW u))
    (lf : FmLaws J Q emb D.what₂.embLL (D.hcW u) D.what₂.places hI hQ) (hO : Q.Over J) : Ch D u :=
  ⟨I.chain emb D.what₂.embLL hI (D.hcW u), J.atT emb D.what₂.embLL hI hJ (D.hcW u) l, Q.per emb D.what₂.embLL hI hQ (D.hcW u),
    forms J Q emb D.what₂.embLL (D.hcW u) Z hI hJ hQ l lf hO⟩

end Chains

section Inputs

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)

@[reducible] def chainOn (rho : ∀ i, (stepAt sel mu cst L Tp u i).Cl → ℂ) (rho' : ∀ i, (stepAt sel mu cst L Tp u (i + 1)).Cl → ℂ)
    (jet : ∀ i, (stepAt sel mu cst L Tp u i).Cl → (stepAt sel mu cst L Tp u (i + 1)).Cl →
      (Pol ℂ X.Tau (R.N i) →ₗ[ℂ] Pol ℂ X.Tau (R.N (i + 1)))) (DG : ℕ) : ChainIn X.E X.K X.Tau R :=
  ⟨stepAt sel mu cst L Tp u, rho, rho', jet, DG⟩

@[reducible] def levelOn {rho rho' jet DG} (psi : ∀ P : Pr.vT u, AddChar (Res P.1) ℂ) (du : ℕ) (Ds Ga : ℝ) :
    AtIn (chainOn sel mu cst L Tp u rho rho' jet DG) :=
  ⟨Pr.T u, Pr.vT u, tdatAt sel mu cst L Tp u, psi, du, Ds, Ga⟩

def ForgetsAt {mu' : Tup X.F X.E X.K S} (cst' : LocCst X (rowSG Pr sel mu'))
    (L' : ChIdx X Pr R (QE sel (mu' : Chr X.F X.E X.K))) (Tp' : TopLev X Pr R (QE sel (mu' : Chr X.F X.E X.K)))
    (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight (R.N 0))
    (e : ((stepAt sel mu cst L Tp u 0).Cl → Fr X.emb σ (R.N 0) → ℂ) ≃ₗ[ℂ]
      ((stepAt sel mu' cst' L' Tp' u 0).Cl → Fr X.emb σ (R.N 0) → ℂ)) : Prop :=
  ForgetsFrames σ lam e

theorem ysAt_zero (N : Submodule (𝓞 X.E) (Sp X.E (R.N 0))) : (ysAt R sel mu cst 0).ys N = {∅} := by
  have h := R.two_le_m
  unfold ysAt
  rw [if_neg (by omega)]
  rfl

variable {sel mu cst L} {Cr : Chars X Pr R.m} {G : ChGlob X R.m} {m2 : ℕ}

end Inputs

section Main

variable {D : D7} {u : D.what₂.Word} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {emb : D.what₂.Tau → E →+* D.what₂.LL} {Pr : Primes (fieldsOver D F E emb)} {u' : Pr.Word}

def SeesAs [Nonempty D.what₂.Tau] (Pr : Primes (fieldsOver D F E emb)) (u' : Pr.Word) (seen : D.what₂.places.Pl → Bool)
    (tau : D.what₂.places.Pl → (Pr.vT u' ≃ D.what₂.Tau)) : Prop :=
  ∀ w, D.what₂.places.resChar w = Pr.T u' → (seen w = true ↔ seenC Pr u' (D.plEq w)) ∧
    ∀ P : Pr.vT u', tau w P = tauOfC (X := fieldsOver D F E emb) (D.plEq w) P.1

variable {Cr : Chars (fieldsOver D F E emb) Pr D.R.m} {sel : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E)} {S : Set ℕ} {m2 : ℕ}
  {mu₀ : Tup F E D.what₂.LL S} {cst₀ : LocCst (fieldsOver D F E emb) (rowSG Pr sel mu₀)}
  {L₀ : ChIdx (fieldsOver D F E emb) Pr D.R (QE (X := fieldsOver D F E emb) sel (mu₀ : Chr F E D.what₂.LL))}
  {Tp₀ : TopLev (fieldsOver D F E emb) Pr D.R (QE (X := fieldsOver D F E emb) sel (mu₀ : Chr F E D.what₂.LL))}
  {G₀ : ChGlob (fieldsOver D F E emb) D.R.m} {rho₀ rho₀' jet₀} {DG₀ : ℕ} {psi₀} {du₀ : ℕ} {Ds₀ Ga₀ : ℝ}
  {Q₀ : PerIn (chainOn (X := fieldsOver D F E emb) sel mu₀ cst₀ L₀ Tp₀ u' rho₀ rho₀' jet₀ DG₀)}
  {Z₀ : FmIn (levelOn (X := fieldsOver D F E emb) sel mu₀ cst₀ L₀ Tp₀ u' (rho := rho₀) (rho' := rho₀') (jet := jet₀) (DG := DG₀)
    psi₀ du₀ Ds₀ Ga₀) D.what₂.places} {hI₀ hJ₀} {hQ₀ : Q₀.Ok} {l₀ lf₀ hO₀}
  {mu : Tup F E D.what₂.LL S} {cst : LocCst (fieldsOver D F E emb) (rowSG Pr sel mu)}
  {L : ChIdx (fieldsOver D F E emb) Pr D.R (QE (X := fieldsOver D F E emb) sel (mu : Chr F E D.what₂.LL))}
  {Tp : TopLev (fieldsOver D F E emb) Pr D.R (QE (X := fieldsOver D F E emb) sel (mu : Chr F E D.what₂.LL))}
  {G : ChGlob (fieldsOver D F E emb) D.R.m} {rho rho' jet} {DG : ℕ} {psi} {du : ℕ} {Ds Ga : ℝ}
  {Q : PerIn (chainOn (X := fieldsOver D F E emb) sel mu cst L Tp u' rho rho' jet DG)}
  {Z : FmIn (levelOn (X := fieldsOver D F E emb) sel mu cst L Tp u' (rho := rho) (rho' := rho') (jet := jet) (DG := DG)
    psi du Ds Ga) D.what₂.places} {hI hJ} {hQ : Q.Ok} {l lf hO}

end Main

end GlobalTheory.LvT.StartTie
