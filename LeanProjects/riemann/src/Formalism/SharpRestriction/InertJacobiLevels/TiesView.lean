import Formalism.SharpRestriction.InertJacobiLevels.TiesCore
import Formalism.SharpRestriction.InertJacobiLevels.TieTTwValsOfMem

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def viewD (D : D7) : GC.GD := ⟨D.R, ⟨D.host.TT, D.host.T2, D.host.u0, D.host.cls⟩, G.hP D⟩

def viewL {D : D7} (L : SizeData₂ D) : GC.GParameters (viewD D) := ⟨L.sc, L.Sc, L.etaSz⟩

def viewX {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : GC.Inst (viewD D) (viewL L) where
  bs := X.bs
  bs_orb := X.bs_orb
  bs_step := X.bs_step
  off := X.off
  off_top := X.off_top
  off_thin := X.off_thin
  off_thick := X.off_thick
  kapI := X.kapI
  ep := X.ep

section View

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ)

theorem partner_view (p : ℕ) (t : G.HH D) (e : ℕ) : G.partner D p t e = GC.partner (viewD D) p t e := rfl

theorem fill_view (j : ℕ) (z : Bool × G.HH D) : G.fill X b j z = GC.fill (viewX X) b j z := rfl

theorem VV_view (p : ℕ) : G.VV X K a b p = GC.VV (viewX X) K a b p := rfl

theorem TTP_view (p : ℕ) : G.TTP X K a b p = GC.TTP (viewX X) K a b p := rfl

theorem tauP_view (p : ℕ) : G.tauP X K a b p = GC.tauP (viewX X) K a b p := rfl

theorem ioP_viewX (p : ℕ) : G.ioP X K a b p = GC.ioP (viewX X) K a b p := rfl

theorem gainP_eq_gainP_viewX (p j : ℕ) : G.gainP X K a b p j = GC.gainP (viewX X) K a b p j := rfl

end View

structure GAll where
  D : GC.GD
  L : GC.GParameters D
  X : GC.Inst D L
  a : GC.HH D → ℤ
  b : GC.HH D → ℤ

theorem GAll.ext_val (A A' : GAll) (hR : A.D.R = A'.D.R)
    (hTT : A.D.host.TT.image Formalism.HC.Frame.A.val = A'.D.host.TT.image Formalism.HC.Frame.A.val)
    (hT2 : A.D.host.T2 = A'.D.host.T2) (hu0 : A.D.host.u0.val = A'.D.host.u0.val)
    (hcls : A.D.host.cls = A'.D.host.cls) (hhP : ∀ p, (A.D.hPf p).val = (A'.D.hPf p).val)
    (hsc : A.L.sc = A'.L.sc) (hSc : A.L.Sc = A'.L.Sc) (heta : A.L.etaSz = A'.L.etaSz)
    (hbs : ∀ (h t : GC.HH A.D) (h' t' : GC.HH A'.D), h.val = h'.val → t.val = t'.val →
      (A.X.bs h t).val = (A'.X.bs h' t').val)
    (hoff : ∀ j c (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.X.off j (c, t) = A'.X.off j (c, t'))
    (hkap : A.X.kapI = A'.X.kapI) (hep : A.X.ep = A'.X.ep)
    (ha : ∀ (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.a t = A'.a t')
    (hb : ∀ (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.b t = A'.b t') : A = A' := by
  obtain ⟨⟨R, ⟨TT, T2, u0, cls⟩, hPf⟩, ⟨sc, Sc, eta⟩,
    ⟨bs, bs_orb, bs_step, off, off_top, off_thin, off_thick, kapI, ep⟩, a, b⟩ := A
  obtain ⟨⟨R', ⟨TT', T2', u0', cls'⟩, hPf'⟩, ⟨sc', Sc', eta'⟩,
    ⟨bs', bs_orb', bs_step', off', off_top', off_thin', off_thick', kapI', ep'⟩, a', b'⟩ := A'
  dsimp only at hR hTT hT2 hu0 hcls hhP hsc hSc heta hbs hoff hkap hep ha hb
  subst hR hT2 hcls hsc hSc heta hkap hep
  have hTTe : TT = TT' := Finset.image_injective (fun x y h => Fin.ext h) hTT
  have hu0e : u0 = u0' := Fin.ext hu0
  have hPfe : hPf = hPf' := funext fun p => Fin.ext (hhP p)
  subst hTTe hu0e hPfe
  have hbse : bs = bs' := funext fun h => funext fun t => Fin.ext (hbs h t h t rfl rfl)
  have hoffe : off = off' := funext fun j => funext fun z => hoff j z.1 z.2 z.2 rfl
  have hae : a = a' := funext fun t => ha t t rfl
  have hbe : b = b' := funext fun t => hb t t rfl
  subst hbse hoffe hae hbe
  rfl

namespace GAll

variable (A : GAll) (K : G.Consts)

def Xpp : ℝ := A.L.sc.X'' A.D.R.n

def wPartV (j tv p e : ℕ) : ℝ := GC.fill A.X A.b j (GC.partner A.D p (A.D.R.ofNat tv) e)

def TTPv (p : ℕ) : Finset ℕ := (GC.TTP A.X K A.a A.b p).image Formalism.HC.Frame.A.val

open Classical in

def gainTotV (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ A.Xpp then 2 * Real.log p *
    ((if GC.IsResidueClassZero A.D p ∨ GC.IsSg A.D p then ∑ j ∈ GC.GParameters.lifts A.D, GC.gainP A.X K A.a A.b p j else 0) -
      GC.tauP A.X K A.a A.b p)
  else 0

open Classical in

def ioTotV (p : ℕ) : ℝ := if (p : ℝ) ≤ A.Xpp then 2 * Real.log p * GC.ioP A.X K A.a A.b p else 0

end GAll

def allOf {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : GAll := ⟨viewD D, viewL L, viewX X, G.aL L, G.bL L⟩

theorem extension_by_zero_val_eq {D D' : D7} {P : Prop} (_he : P)
    (hTT : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val) (f : D.host.TT → ℤ) (f' : D'.host.TT → ℤ)
    (hf : ∀ (t : D.host.TT) (t' : D'.host.TT), (t : D.R.A).val = (t' : D'.R.A).val → f t = f' t')
    (t : G.HH D) (t' : G.HH D') (ht : t.val = t'.val) :
    (if h : t ∈ D.host.TT then f ⟨t, h⟩ else 0) = (if h : t' ∈ D'.host.TT then f' ⟨t', h⟩ else 0) := by

  have key : ∀ {E E' : D7} (s : G.HH E) (s' : G.HH E'),
      E.host.TT.image Formalism.HC.Frame.A.val = E'.host.TT.image Formalism.HC.Frame.A.val →
      s.val = s'.val → s ∈ E.host.TT → s' ∈ E'.host.TT := by
    intro E E' s s' hT hs hm
    have h1 : s.val ∈ E'.host.TT.image Formalism.HC.Frame.A.val := by
      rw [← hT]
      exact Finset.mem_image_of_mem _ hm
    obtain ⟨u, hu, hu'⟩ := Finset.mem_image.mp h1
    have hus : u = s' := Fin.ext (hu'.trans hs)
    exact hus ▸ hu
  by_cases h : t ∈ D.host.TT
  · have h' := key t t' hTT ht h
    rw [dif_pos h, dif_pos h']
    exact hf ⟨t, h⟩ ⟨t', h'⟩ ht
  · have h' : t' ∉ D'.host.TT := fun h' => h (key t' t hTT.symm ht.symm h')
    rw [dif_neg h, dif_neg h']

theorem host_cls_eq {R R' : Ranks} {H : Host R} {H' : Host R'} (hq : H.q = H'.q) (hd : H.d = H'.d)
    (hQS : H.QS = H'.QS) : H.cls = H'.cls := by
  have hN : H.toHostRaw.condN = H'.toHostRaw.condN := by
    simp only [Formalism.HC.HostRaw.condN, hq, hd, hQS]

  have hps : ∀ p, H.toHostRaw.psAt p = H'.toHostRaw.psAt p := by
    intro p
    unfold Formalism.HC.HostRaw.psAt
    by_cases hc : Nat.Coprime p H.toHostRaw.condN
    · have hc' : Nat.Coprime p H'.toHostRaw.condN := by
        rw [← hN]
        exact hc
      rw [dif_pos hc, dif_pos hc']
      have e := H.flPS (ZMod.unitOfCoprime p hc)
      have e' := H'.flPS (ZMod.unitOfCoprime p hc')
      rw [e, e']
      simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Formalism.HC.HostRaw.condN, hq, hd, hQS]
    · have hc' : ¬ Nat.Coprime p H'.toHostRaw.condN := by
        rw [← hN]
        exact hc
      rw [dif_neg hc, dif_neg hc']
  funext p
  unfold Formalism.BasicNotions.Host.cls Formalism.BasicNotions.primeClass
  rw [hps p]
  simp only [Formalism.HC.HostRaw.small, hq, hd, hQS]
  split_ifs <;> simp_all

theorem allOf_eq {D D' : D7} {L : SizeData₂ D} {L' : SizeData₂ D'} (X : G.Inst D L) (X' : G.Inst D' L')
    (hR : D.R = D'.R) (hTT : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val)
    (hT2 : D.host.T2 = D'.host.T2) (hu0 : D.host.u0.val = D'.host.u0.val)
    (hcls : D.host.cls = D'.host.cls)
    (hhP : ∀ p, (G.hP D p).val = (G.hP D' p).val)
    (hsc : L.sc = L'.sc) (hSc : L.Sc = L'.Sc) (heta : L.etaSz = L'.etaSz)
    (hbs : ∀ (h t : G.HH D) (h' t' : G.HH D'), h.val = h'.val → t.val = t'.val → (X.bs h t).val = (X'.bs h' t').val)
    (hoff : ∀ j c (t : G.HH D) (t' : G.HH D'), t.val = t'.val → X.off j (c, t) = X'.off j (c, t'))
    (hkap : X.kapI = X'.kapI) (hep : X.ep = X'.ep)
    (haT : ∀ (t : D.host.TT) (t' : D'.host.TT), (t : D.R.A).val = (t' : D'.R.A).val →
      L.aT t = L'.aT t')
    (hbT : ∀ (t : D.host.TT) (t' : D'.host.TT), (t : D.R.A).val = (t' : D'.R.A).val →
      L.bT t = L'.bT t') : allOf X = allOf X' := by
  refine GAll.ext_val _ _ hR hTT hT2 hu0 hcls hhP hsc hSc heta hbs hoff hkap hep ?_ ?_
  · intro t t' ht
    exact extension_by_zero_val_eq hR hTT _ _ haT t t' ht
  · intro t t' ht
    exact extension_by_zero_val_eq hR hTT _ _ hbT t t' ht

section Tied

variable {D : D7} (L0 : SizeData₂ D) (X0 : G.Inst D L0) (K : G.Consts) (dr : Set ℕ)
  (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
  (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
  (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)

theorem tie_wPart_V (j : ℕ) (t : D.host.TT) (p e : ℕ) :
    (tieWeightData L0 X0 K dr len hw hg hu).wPart j t p e =
      (allOf X0).wPartV j (t : D.R.A).val p e := by
  have hof : D.R.ofNat ((t : D.R.A).val) = (t : D.R.A) := by
    apply Fin.ext
    simp [Formalism.HC.Frame.ofNat, Formalism.HC.Frame.A.ofVal, Formalism.HC.Frame.A.val]
    exact Nat.mod_eq_of_lt (t : D.R.A).2
  show G.fill X0 (G.bL L0) j (G.partner D p t e) =
    GC.fill (viewX X0) (G.bL L0) j (GC.partner (viewD D) p (D.R.ofNat (t : D.R.A).val) e)
  rw [hof, fill_view, partner_view]

theorem tie_gainTot_V (p : ℕ) (hp : p.Prime) :
    gainTot (tieWeightData L0 X0 K dr len hw hg hu) p = (allOf X0).gainTotV K p := by
  by_cases h : (p : ℝ) ≤ L0.sc.X'' D.R.n
  · rw [tie_gainTot_below L0 X0 K dr len hw hg hu p hp h]
    exact (if_pos h).symm
  · rw [tie_gainTot_above L0 X0 K dr len hw hg hu p (not_le.1 h)]
    exact (if_neg h).symm

theorem tie_ioTot_V (p : ℕ) (hp : p.Prime) :
    ioTot (tieWeightData L0 X0 K dr len hw hg hu) p = (allOf X0).ioTotV K p := by
  by_cases h : (p : ℝ) ≤ L0.sc.X'' D.R.n
  · rw [tie_ioTot_below L0 X0 K dr len hw hg hu p hp h]
    exact (if_pos h).symm
  · rw [tie_ioTot_above L0 X0 K dr len hw hg hu p (not_le.1 h)]
    exact (if_neg h).symm

open Classical in
theorem tie_TTwVals_V (p : ℕ) (hp : p.Prime) :
    TTwVals (tieWeightData L0 X0 K dr len hw hg hu) p = if UnderSupp L0 p then {(allOf X0).TTPv K p} else ∅ :=
  tie_TTwVals L0 X0 K dr len hw hg hu p hp

end Tied

theorem tie_invariance {D D' : D7} (L0 : SizeData₂ D) (L0' : SizeData₂ D') (X0 : G.Inst D L0) (X0' : G.Inst D' L0')
    (K : G.Consts) (dr dr' : Set ℕ) (len : D.what₂.Word → D.what₂.places.Pl → ℚ)
    (len' : D'.what₂.Word → D'.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n) (hw' : 1 ≤ L0'.sc.w'' D'.R.n)
    (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
    (hg' : ∀ i, ¬ (G.IsResidueClassZero D' (D'.host.g i) ∨ G.IsSg D' (D'.host.g i)))
    (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)
    (hu' : ∀ w, D'.what₂.muAt w = D'.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D'.R.m → Fval L0' j w = 0)
    (hA : allOf X0 = allOf X0') :
    (∀ (t : D.host.TT) (t' : D'.host.TT), (t : D.R.A).val = (t' : D'.R.A).val →
      ∀ j p e, (tieWeightData L0 X0 K dr len hw hg hu).wPart j t p e =
        (tieWeightData L0' X0' K dr' len' hw' hg' hu').wPart j t' p e) ∧
    ∀ p : ℕ, p.Prime →
      gainTot (tieWeightData L0 X0 K dr len hw hg hu) p = gainTot (tieWeightData L0' X0' K dr' len' hw' hg' hu') p ∧
      ioTot (tieWeightData L0 X0 K dr len hw hg hu) p = ioTot (tieWeightData L0' X0' K dr' len' hw' hg' hu') p ∧
      ((UnderSupp L0 p ↔ UnderSupp L0' p) →
        TTwVals (tieWeightData L0 X0 K dr len hw hg hu) p = TTwVals (tieWeightData L0' X0' K dr' len' hw' hg' hu') p) := by
  classical
  refine ⟨fun t t' ht j p e => ?_, fun p hp => ⟨?_, ?_, fun hU => ?_⟩⟩
  · rw [tie_wPart_V, tie_wPart_V, hA, ht]
  · rw [tie_gainTot_V _ _ _ _ _ _ _ _ p hp, tie_gainTot_V _ _ _ _ _ _ _ _ p hp, hA]
  · rw [tie_ioTot_V _ _ _ _ _ _ _ _ p hp, tie_ioTot_V _ _ _ _ _ _ _ _ p hp, hA]
  · rw [tie_TTwVals_V _ _ _ _ _ _ _ _ p hp, tie_TTwVals_V _ _ _ _ _ _ _ _ p hp, hA]
    by_cases h : UnderSupp L0 p
    · rw [if_pos h, if_pos (hU.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hU.2 h'))]

end Formalism.MainNotions.Inhab

end
