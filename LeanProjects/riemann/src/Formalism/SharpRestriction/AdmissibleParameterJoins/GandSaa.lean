import Formalism.SharpRestriction.InertJacobiLevels.TiesView
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab

def SameServed (K : G.Consts) (A A' : GAll) (p : ℕ) : Prop :=
  (GC.VV A.X K A.a A.b p).image Formalism.HC.Frame.A.val = (GC.VV A'.X K A'.a A'.b p).image Formalism.HC.Frame.A.val ∧
  GC.Sig A.X K A.a A.b p = GC.Sig A'.X K A'.a A'.b p ∧
  GC.tauP A.X K A.a A.b p = GC.tauP A'.X K A'.a A'.b p ∧
  GC.ioP A.X K A.a A.b p = GC.ioP A'.X K A'.a A'.b p ∧
  ∀ t0 ∈ GC.VV A.X K A.a A.b p, ∀ t0' : GC.HH A'.D, t0.val = t0'.val →
    GC.kapv A.X K A.a A.b p t0 = GC.kapv A'.X K A'.a A'.b p t0' ∧
    GC.Sv A.X K A.a A.b p t0 = GC.Sv A'.X K A'.a A'.b p t0'

theorem sameServed (K : G.Consts) (A A' : GAll) (hR : A.D.R = A'.D.R)
    (hTT : A.D.host.TT.image Formalism.HC.Frame.A.val = A'.D.host.TT.image Formalism.HC.Frame.A.val)
    (hcls : A.D.host.cls = A'.D.host.cls) (hhP : ∀ p, (A.D.hPf p).val = (A'.D.hPf p).val)
    (hsc : A.L.sc = A'.L.sc) (hSc : A.L.Sc = A'.L.Sc) (heta : A.L.etaSz = A'.L.etaSz)
    (hbs : ∀ (h t : GC.HH A.D) (h' t' : GC.HH A'.D), h.val = h'.val → t.val = t'.val →
      (A.X.bs h t).val = (A'.X.bs h' t').val)
    (hoff : ∀ j (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.X.off j (false, t) = A'.X.off j (false, t'))
    (hkap : A.X.kapI = A'.X.kapI) (hep : A.X.ep = A'.X.ep)
    (ha : ∀ (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.a t = A'.a t')
    (hb : ∀ (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.b t = A'.b t') (p : ℕ) :
    SameServed K A A' p := by
  obtain ⟨⟨R, ⟨TT, T2, u0, cls⟩, hPf⟩, ⟨sc, Sc, η⟩, ⟨bs, h1, h2, off, h3, h4, h5, kapI, ep⟩, a, b⟩ := A
  obtain ⟨⟨R', ⟨TT', T2', u0', cls'⟩, hPf'⟩, ⟨sc', Sc', η'⟩, ⟨bs', h1', h2', off', h3', h4', h5', kapI', ep'⟩, a', b'⟩ := A'
  simp only at hR
  subst hR
  simp only at hTT hcls hhP hsc hSc heta hbs hoff hkap hep ha hb
  have eTT : TT = TT' := Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have ehP : hPf = hPf' := funext fun p => Formalism.HC.Frame.A.val_injective _ (hhP p)
  have ebs : bs = bs' := funext fun h => funext fun t => Formalism.HC.Frame.A.val_injective _ (hbs h t h t rfl rfl)
  have ea : a = a' := funext fun t => ha t t rfl
  have eb : b = b' := funext fun t => hb t t rfl
  subst eTT hcls ehP hsc hSc heta ebs hkap hep ea eb
  have hoff' : ∀ j t, off j (false, t) = off' j (false, t) := fun j t => hoff j t t rfl
  let D1 : GC.GD := ⟨R, ⟨TT, T2, u0, cls⟩, hPf⟩
  let D2 : GC.GD := ⟨R, ⟨TT, T2', u0', cls⟩, hPf⟩
  let X1 : GC.Inst D1 ⟨sc, Sc, η⟩ := ⟨bs, h1, h2, off, h3, h4, h5, kapI, ep⟩
  let X2 : GC.Inst D2 ⟨sc, Sc, η⟩ := ⟨bs, h1', h2', off', h3', h4', h5', kapI, ep⟩
  have eVV : GC.VV X1 K a b p = GC.VV X2 K a b p := rfl
  have eSig : GC.Sig X1 K a b p = GC.Sig X2 K a b p := rfl
  have eTau : GC.tauP X1 K a b p = GC.tauP X2 K a b p := rfl
  have eKap : ∀ t0, GC.kapv X1 K a b p t0 = GC.kapv X2 K a b p t0 := fun _ => rfl
  have eSv : cls p = PrimeClass.inertClass → ∀ t0, GC.Sv X1 K a b p t0 = GC.Sv X2 K a b p t0 := by
    intro hc0 t0
    have hp1 : ∀ s e, GC.partner D1 p s e = (false, s + e • hPf p) := by
      intro s e
      show (decide (cls p = PrimeClass.signal ∧ Odd e), s + e • hPf p) = _
      simp [hc0]
    have hp2 : ∀ s e, GC.partner D2 p s e = (false, s + e • hPf p) := by
      intro s e
      show (decide (cls p = PrimeClass.signal ∧ Odd e), s + e • hPf p) = _
      simp [hc0]
    have hfG : ∀ j s, GC.fillG X1 b j (false, s) = GC.fillG X2 b j (false, s) := by
      intro j s
      show (_ + off j (false, s)) - _ = (_ + off' j (false, s)) - _
      rw [hoff']
      rfl
    have hcap : ∀ j s e, GC.capU X1 b p j s e = GC.capU X2 b p j s e := by
      intro j s e
      unfold GC.capU
      rw [hp1, hp2, hfG]
      rfl
    unfold GC.Sv GC.gU GC.g0 GC.Pr
    simp only [hcap, hfG]
    rfl
  have hC0 : (GC.VV X1 K a b p).Nonempty → cls p = PrimeClass.inertClass := by
    intro hne
    by_contra hn
    have : GC.VV X1 K a b p = ∅ := by
      unfold GC.VV
      rw [if_neg]
      rintro ⟨hc, _⟩
      exact hn hc.2.2.1
    rw [this] at hne
    exact Finset.not_nonempty_empty hne
  refine ⟨congrArg (Finset.image Formalism.HC.Frame.A.val) eVV, eSig, eTau, ?_, ?_⟩
  · show GC.ioP X1 K a b p = GC.ioP X2 K a b p
    by_cases hne : (GC.VV X1 K a b p).Nonempty
    · have hne2 : (GC.VV X2 K a b p).Nonempty := hne
      unfold GC.ioP
      rw [dif_pos hne, dif_pos hne2, eSig]
      congr 1
      exact Finset.sup'_congr hne rfl fun t0 _ => eSv (hC0 hne) t0
    · have hne2 : ¬ (GC.VV X2 K a b p).Nonempty := hne
      unfold GC.ioP
      rw [dif_neg hne, dif_neg hne2]
  · show ∀ t0 ∈ GC.VV X1 K a b p, ∀ t0' : GC.HH D2, t0.val = t0'.val →
      GC.kapv X1 K a b p t0 = GC.kapv X2 K a b p t0' ∧ GC.Sv X1 K a b p t0 = GC.Sv X2 K a b p t0'
    intro t0 ht0 t0' htt
    have : t0 = t0' := Formalism.HC.Frame.A.val_injective _ htt
    subst this
    exact ⟨eKap t0, eSv (hC0 ⟨t0, ht0⟩) t0⟩

variable {eps : ℝ} (Fm : FamP eps)

theorem served_orbit_counts_agree (x : ℝ) (hx : Fm.x1 < x) : Formalism.MainNotions.LocalQuadraticParts.AmbientMetricLowerBound Fm x := by
  intro i i' a b u0 u0' hr hr' p
  have hTT : (Fm.D x i).host.TT.image Formalism.HC.Frame.A.val = (Fm.D x i').host.TT.image Formalism.HC.Frame.A.val :=
    (Fm.TT_eq x i).trans (Fm.TT_eq x i').symm
  have hR := Fm.R_eq x i i'
  have hsc : (Fm.L x i).sc = (Fm.L x i').sc := by
    have e1 : (Fm.L x i).sc.x = (Fm.L x i').sc.x := by rw [Fm.L_x x i hx, Fm.L_x x i' hx]
    have e2 : (Fm.L x i).sc.eps = (Fm.L x i').sc.eps := by rw [Fm.L_eps x i, Fm.L_eps x i']
    have e3 : (Fm.L x i).sc.J = (Fm.L x i').sc.J := (Fm.L_J x i).trans (Fm.L_J x i').symm
    cases h1 : (Fm.L x i).sc
    cases h2 : (Fm.L x i').sc
    rw [h1, h2] at e1 e2 e3
    simp only at e1 e2 e3
    subst e1 e2 e3
    rfl
  exact sameServed Fm.GK (allOf (Fm.Gx x i)) (allOf (Fm.Gx x i')) hR hTT
    (host_cls_eq (Fm.q_eq x i i') (Fm.d_eq x i i') (Fm.QS_eq x i i'))
    (Fm.hP_eq x i i') hsc (Fm.Sc_shared x i i') (Fm.eta_eq x i i') (Fm.bs_eq x i i') (Fm.off_eq x i i')
    (Fm.kapI_eq x i i') (Fm.ep_eq x i i')
    (fun t t' ht => extension_by_zero_val_eq (congrArg (fun R : Ranks => R.e) hR) hTT _ _
      (fun s s' hs => by rw [(hr.2 s).1, (hr'.2 s').1, hs]) t t' ht)
    (fun t t' ht => extension_by_zero_val_eq (congrArg (fun R : Ranks => R.e) hR) hTT _ _
      (fun s s' hs => by rw [(hr.2 s).2, (hr'.2 s').2, hs]) t t' ht) p

theorem family_served_orbit_counts_agree : Formalism.MainNotions.LocalQuadraticParts.BaseIndependenceFamily Fm := fun x hx => served_orbit_counts_agree Fm x hx

end Formalism.MainNotions.J
