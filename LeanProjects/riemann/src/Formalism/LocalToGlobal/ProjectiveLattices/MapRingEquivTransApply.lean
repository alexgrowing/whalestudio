import Formalism.LocalToGlobal.ProjectiveLattices.XcLat

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem host_ext {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (hd : H.d = H'.d) (hrt : H.rt = H'.rt)
    (hrt0 : H.rt0 = H'.rt0) : H = H' := by
  obtain ⟨d, _, _, rt, _, w0, tw, bar, be, _, rt0, _⟩ := H
  obtain ⟨d', _, _, rt', _, w0', tw', bar', be', _, rt0', _⟩ := H'
  simp only at hd hrt hrt0
  subst hd hrt hrt0
  have hw : w0 = w0' := by
    apply RingOfIntegers.ext
    have h2 := congrArg (fun x : 𝓞 E => (x : E)) (tw.trans tw'.symm)
    simp only [map_mul, map_ofNat] at h2
    exact mul_left_cancel₀ two_ne_zero h2
  have hb : bar = bar' := RingEquiv.ext fun a => RingOfIntegers.ext ((be a).trans (be' a).symm)
  subst hw hb
  rfl

theorem level_ext {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l l' : Level H} (hM : l.M = l'.M) (hMb : l.Mb = l'.Mb)
    (hA : l.A = l'.A) : l = l' := by
  obtain ⟨M, _, _, Mb, _, _, _, A, _⟩ := l
  obtain ⟨M', _, _, Mb', _, _, _, A', _⟩ := l'
  simp only at hM hMb hA
  subst hM hMb hA
  rfl

theorem coeff_ext {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c c' : Coeff l} (h : c.F = c'.F) : c = c' := by
  obtain ⟨F, _, _, _, _⟩ := c
  obtain ⟨F', _, _, _, _⟩ := c'
  simp only at h
  subst h
  rfl

end Ext

variable {D : D7}

namespace Par

theorem coe_mem_of_pinField {Q Q' : Par D} (h : Q.PinField) (h' : Q'.PinField) (a : 𝓞 Q.c.F) :
    ((a : Q.c.F) : ℂ) ∈ Q'.c.F := by
  have e1 := h a
  have e2 := h' (Q'.eO.symm (Q.eO a))
  rw [RingEquiv.apply_symm_apply] at e2
  rw [← e1, e2]
  exact SetLike.coe_mem _

theorem F_le {Q Q' : Par D} (h : Q.PinField) (h' : Q'.PinField) : Q.c.F ≤ Q'.c.F := by
  intro x hx
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨x, hx⟩ : Q.c.F)
  have hx' : x = ((algebraMap (𝓞 Q.c.F) Q.c.F a : Q.c.F) : ℂ) / ((algebraMap (𝓞 Q.c.F) Q.c.F b : Q.c.F) : ℂ) := by
    rw [← IntermediateField.coe_div, hab]
  rw [hx']
  exact div_mem (coe_mem_of_pinField h h' a) (coe_mem_of_pinField h h' b)

theorem F_eq {Q Q' : Par D} (h : Q.PinField) (h' : Q'.PinField) : Q.c.F = Q'.c.F :=
  le_antisymm (F_le h h') (F_le h' h)

end Par

open Classical in

def NlM {T : Core D} (h : LawsM T) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  if hj : InR D j then
    l2C (T.U j) (goodOf T.Q.c σ) (T.V j _) (T.dict j _) (T.mu j _) (xiR D) (wtA w) w.n
      (h.cuspidalL2Subspace j hj _ (goodEmb_goodOf _ σ) _ _ (dom_wtA w))
  else 0

structure IsCoreIso {T T' : Core D} (h : LawsM T) (h' : LawsM T') (j : ℕ) (fe : T.Q.c.F ≃+* T'.Q.c.F)
    (Φ : T.R j ≃+* T'.R j) (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)) : Prop where
  fe_coe : ∀ x, ((fe x : T'.Q.c.F) : ℂ) = x
  smul : ∀ (a : T.Q.c.F) (f : T.R j), Φ (a • f) = fe a • Φ f
  eO : ∀ x, T'.Q.eO (RingOfIntegers.mapRingEquiv fe x) = T.Q.eO x
  pl_bij : Function.Bijective pl
  pl_mem : ∀ la x, x ∈ la.asIdeal ↔ RingOfIntegers.mapRingEquiv fe x ∈ (pl la).asIdeal
  pl_norm : ∀ la, Ideal.absNorm (pl la).asIdeal = Ideal.absNorm la.asIdeal
  cusp : ∀ (w : WeightFamilies.Wt D j) (f : T.R j), f ∈ T.C j w ↔ Φ f ∈ T'.C j w
  vals : ∀ la (v : T.R j → EReal), v ∈ T.Vs j la ↔ v ∘ Φ.symm ∈ T'.Vs j (pl la)
  sup : ∀ (w : WeightFamilies.Wt D j) (σ : T'.Q.c.F →+* ℂ) (f : T.R j), f ∈ T.C j w →
    T'.Ns j w σ (Φ f) = T.Ns j w (σ.comp fe.toRingHom) f
  l2 : ∀ (w : WeightFamilies.Wt D j) (σ : T'.Q.c.F →+* ℂ) (f : T.R j), f ∈ T.C j w →
    NlM h' j w σ (Φ f) = NlM h j w (σ.comp fe.toRingHom) f

theorem mapRingEquiv_refl_apply {K : Type} [Field K] (x : 𝓞 K) : RingOfIntegers.mapRingEquiv (RingEquiv.refl K) x = x :=
  RingOfIntegers.ext rfl

theorem mapRingEquiv_trans_apply {K K' K'' : Type} [Field K] [Field K'] [Field K''] (e : K ≃+* K') (e' : K' ≃+* K'')
    (x : 𝓞 K) :
    RingOfIntegers.mapRingEquiv (e.trans e') x = RingOfIntegers.mapRingEquiv e' (RingOfIntegers.mapRingEquiv e x) :=
  RingOfIntegers.ext rfl

theorem comp_refl_eq {K : Type} [Field K] (σ : K →+* ℂ) : σ.comp (RingEquiv.refl K).toRingHom = σ :=
  RingHom.ext fun _ => rfl

theorem comp_trans_eq {K K' K'' : Type} [Field K] [Field K'] [Field K''] (e : K ≃+* K') (e' : K' ≃+* K'')
    (σ : K'' →+* ℂ) : (σ.comp e'.toRingHom).comp e.toRingHom = σ.comp (e.trans e').toRingHom :=
  RingHom.ext fun _ => rfl

theorem IsCoreIso.trans {T T' T'' : Core D} {h : LawsM T} {h' : LawsM T'} {h'' : LawsM T''} {j : ℕ}
    {fe : T.Q.c.F ≃+* T'.Q.c.F} {Φ : T.R j ≃+* T'.R j}
    {pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)}
    {fe' : T'.Q.c.F ≃+* T''.Q.c.F} {Φ' : T'.R j ≃+* T''.R j}
    {pl' : HeightOneSpectrum (𝓞 T'.Q.c.F) → HeightOneSpectrum (𝓞 T''.Q.c.F)}
    (A : IsCoreIso h h' j fe Φ pl) (B : IsCoreIso h' h'' j fe' Φ' pl') :
    IsCoreIso h h'' j (fe.trans fe') (Φ.trans Φ') (pl' ∘ pl) where
  fe_coe x := (B.fe_coe _).trans (A.fe_coe x)
  smul a f := by
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, A.smul, B.smul]
    rfl
  eO x := by rw [mapRingEquiv_trans_apply, B.eO, A.eO]
  pl_bij := B.pl_bij.comp A.pl_bij
  pl_mem la x := by rw [A.pl_mem, B.pl_mem, mapRingEquiv_trans_apply]; rfl
  pl_norm la := (B.pl_norm (pl la)).trans (A.pl_norm la)
  cusp w f := (A.cusp w f).trans (B.cusp w _)
  vals la v := (A.vals la v).trans (B.vals (pl la) _)
  sup w σ f hf := by
    rw [RingEquiv.trans_apply, B.sup w σ _ ((A.cusp w f).1 hf), A.sup w _ f hf, comp_trans_eq]
  l2 w σ f hf := by
    rw [RingEquiv.trans_apply, B.l2 w σ _ ((A.cusp w f).1 hf), A.l2 w _ f hf, comp_trans_eq]

def IsCoreIso.ptEquiv {T T' : Core D} {h : LawsM T} {h' : LawsM T'} {j : ℕ} {fe : T.Q.c.F ≃+* T'.Q.c.F}
    {Φ : T.R j ≃+* T'.R j} {pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)}
    (A : IsCoreIso h h' j fe Φ pl) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : T.PtM j la ≃ T'.PtM j (pl la) where
  toFun y := ⟨y.1 ∘ Φ.symm, (A.vals la y.1).1 y.2⟩
  invFun z := ⟨z.1 ∘ Φ, (A.vals la _).2 (by
    have e : (z.1 ∘ Φ) ∘ Φ.symm = z.1 := funext fun x => by simp
    rw [e]; exact z.2)⟩
  left_inv y := Subtype.ext (funext fun x => by simp)
  right_inv z := Subtype.ext (funext fun x => by simp)

def CxIndep (D : D7) : Prop :=
  ∀ (T : Core D) (U : ∀ j (σ : T.Q.c.F →+* ℂ), Unf (T.Q.Xo j) T.Q.c σ D.R.r) (V : ℕ → (T.Q.c.F →+* ℂ) → HSp D)
    (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
    (Kf : ∀ j σ, Subgroup (GA D (V j σ))) (h : LawsM T)
    (h' : LawsM { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf }) (j : ℕ), InR D j →
    ∀ w : WeightFamilies.Wt D j, T.C j w = Core.C { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf } j w ∧
      ∀ (σ : T.Q.c.F →+* ℂ), ∀ f ∈ T.C j w,
        T.Ns j w σ f = Core.Ns { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf } j w σ f ∧
        NlM h j w σ f = NlM h' j w σ f

theorem isCoreIso_of_cx (hc : CxIndep D) (T : Core D) (U : ∀ j (σ : T.Q.c.F →+* ℂ), Unf (T.Q.Xo j) T.Q.c σ D.R.r)
    (V : ℕ → (T.Q.c.F →+* ℂ) → HSp D) (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r)
    (mu : ∀ j σ, GA D (V j σ) → ℂ) (Kf : ∀ j σ, Subgroup (GA D (V j σ))) (h : LawsM T)
    (h' : LawsM { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf }) (j : ℕ) (hj : InR D j) :
    IsCoreIso h h' j (RingEquiv.refl _) (RingEquiv.refl _) id where
  fe_coe _ := rfl
  smul _ _ := rfl
  eO x := by rw [mapRingEquiv_refl_apply]
  pl_bij := Function.bijective_id
  pl_mem la x := by rw [mapRingEquiv_refl_apply]; rfl
  pl_norm _ := rfl
  cusp w f := by rw [(hc T U V dict mu Kf h h' j hj w).1]; rfl
  vals _ _ := Iff.rfl
  sup w σ f hf := by rw [comp_refl_eq]; exact ((hc T U V dict mu Kf h h' j hj w).2 σ f hf).1.symm
  l2 w σ f hf := by rw [comp_refl_eq]; exact ((hc T U V dict mu Kf h h' j hj w).2 σ f hf).2.symm

def ParTr (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsCore T) (_h' : LawsCore T') (j : ℕ), InR D j →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsCore { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)),
      IsCoreIso _h.toLawsM h''.toLawsM j fe Φ pl

def INV (D : D7) : Prop :=
  ∀ (T T' : Core D) (h : LawsCore T) (h' : LawsCore T') (j : ℕ), InR D j →
    ∃ (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso h.toLawsM h'.toLawsM j fe Φ pl

theorem inv_of (hp : ParTr D) (hc : CxIndep D) : INV D := by
  intro T T' h h' j hj
  obtain ⟨U, V, dict, mu, Kf, h'', fe, Φ, pl, A⟩ := hp T T' h h' j hj
  exact ⟨_, _, _, A.trans (isCoreIso_of_cx hc { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf } T'.U T'.V T'.dict T'.mu
    T'.Kf h''.toLawsM h'.toLawsM j hj)⟩

def ParTrPb (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsM T) (_h' : LawsM T'), T.pb = T'.pb → ∀ (j : ℕ), InR D j →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsM { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso _h h'' j fe Φ pl

def INVPb (D : D7) : Prop :=
  ∀ (T T' : Core D) (h : LawsM T) (h' : LawsM T'), T.pb = T'.pb → ∀ (j : ℕ), InR D j →
    ∃ (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso h h' j fe Φ pl

end Formalism.L2.Pj
