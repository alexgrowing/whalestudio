import Formalism.SharpRestriction.InertJacobiLevels.TiesView
import Formalism.SharpRestriction.InertJacobiLevels.LambdaRealEqShiftedWeight

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

abbrev KapI : Type := ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ

theorem not_inert_of_jacobi (D : D7) (p : ℕ) (h2 : p ≠ 2) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d)
    (hj : jacobiSym (-(D.host.d : ℤ)) p = 1) : ¬ (G.IsResidueClassZero D p ∨ G.IsSg D p) := by
  by_cases hs : p ∈ D.host.small
  · have h : D.host.cls p = PrimeClass.ram2 := if_pos hs
    rintro (h' | h')
    · exact PrimeClass.noConfusion (h.symm.trans h')
    · exact PrimeClass.noConfusion (h.symm.trans h')
  have h : D.host.cls p = PrimeClass.splitK := by
    unfold Host.cls primeClass
    rw [if_neg hs, if_neg hq, if_neg hd, if_pos hj]
  rintro (h' | h')
  · have h'' : D.host.cls p = PrimeClass.inertClass := h'
    rw [h] at h''
    exact PrimeClass.noConfusion h''
  · have h'' : D.host.cls p = PrimeClass.signal := h'
    rw [h] at h''
    exact PrimeClass.noConfusion h''

structure LatIn (D : D7) where
  Vram : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn
  len : D.what₂.Word → D.what₂.places.Pl → ℚ

def LatIn.zero (D : D7) : LatIn D := ⟨fun _ _ _ => ⊥, fun _ _ => 0⟩

structure TieHyp {D : D7} (gatT : GatTies D) (L0 : SizeData₂ D) (kapI : KapI) (ep : ℕ → ℕ) where

  hw : 1 ≤ L0.sc.w'' D.R.n

  hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i))

  hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0

  htw : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L0.sc.X'' D.R.n ∨
    D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) ∨ w ∈ L0.supp

  pos : PosHyp gatT (instW L0 kapI ep)

  c : ℕ
  c_le : (c : ℝ) ≤ G.cG L0
  hcl : L0.Sc + ((D.R.k : ℝ) - 1) / 2 ≤ c

  hoff : ∀ u τ, (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → ∀ i : Fin D.R.k,
    |(((D.hcW u τ).u i : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c

  hw1 : ∀ τ, (c : ℝ) ≤ wj D 1 τ - G.kaJ D 1

namespace TieHyp

variable {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ} (H : TieHyp gatT L0 kapI ep)
  (K : G.Consts) (Cr : ℝ) (Λ : LatIn D)

def L : SizeData₂ D := tieL L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu

def Gx : G.Inst D (H.L K Cr Λ) := tieX L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu

def posL : PosHyp gatT (H.Gx K Cr Λ) where
  vOf := H.pos.vOf
  inj := H.pos.inj
  n_eq := H.pos.n_eq
  pos := H.pos.pos
  r_eq := H.pos.r_eq

def latHyp : LatHyp gatT (H.Gx K Cr Λ) := latHypOf gatT (H.Gx K Cr Λ) (H.posL K Cr Λ) H.c H.c_le H.hcl H.hoff H.hw1

def Gy : G.LatInst D := { (H.latHyp K Cr Λ).latInst with Vram := Λ.Vram }

theorem supp_sat (w : D.what₂.places.Pl) (h : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ (H.L K Cr Λ).sc.X'' D.R.n) :
    w ∈ (H.L K Cr Λ).supp :=
  tieL_supp_sat L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu w h

theorem tw_supp (w : D.what₂.places.Pl) (h : D.what₂.muAt w ≠ D.what₂.mu0) : w ∈ (H.L K Cr Λ).supp :=
  (mem_tieSupp L0 w).2 (H.htw w h)

theorem fills (w : D.what₂.places.Pl) : G.ParametersFill (H.Gx K Cr Λ) K w :=
  tieL_fills L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu (instW_fill L0 kapI ep) w

theorem lats_zero (w : D.what₂.places.Pl) :
    G.LatticeLengthsAtPlace (H.Gx K Cr (LatIn.zero D)) (H.Gy K Cr (LatIn.zero D)) K w :=
  sizeDataLat_of_Vram_bot _ _ _ (fun _ _ _ => rfl) (fun _ _ => rfl) w

theorem lenMN_eq : (H.L K Cr Λ).lenMN = Λ.len := rfl

theorem latTied : G.LatTied gatT (H.Gx K Cr Λ) (H.Gy K Cr Λ) := (H.latHyp K Cr Λ).latTied (instW_fill L0 kapI ep)

theorem drop_iff (p : ℕ) :
    p ∈ (H.L K Cr Λ).drop ↔ NoGain (H.Gx K Cr Λ) K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T :=
  tieL_drop_iff L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu p

theorem L_FDef : (H.L K Cr Λ).FDef := tie_FDef L0 (instW L0 kapI ep) K _ Λ.len H.hw H.hg H.hu

theorem L_keeps : (H.L K Cr Λ).sc = L0.sc ∧ (H.L K Cr Λ).aT = L0.aT ∧ (H.L K Cr Λ).bT = L0.bT ∧ (H.L K Cr Λ).etaSz = L0.etaSz ∧
    (H.L K Cr Λ).Sc = L0.Sc ∧ (H.L K Cr Λ).Cc = L0.Cc ∧ (H.L K Cr Λ).Ct = L0.Ct ∧ (H.L K Cr Λ).CGam = L0.CGam ∧
    (H.L K Cr Λ).de2 = L0.de2 ∧ (H.L K Cr Λ).j0 = L0.j0 ∧ (H.L K Cr Λ).E = L0.E ∧ (H.L K Cr Λ).NuLat = L0.NuLat ∧
    (H.L K Cr Λ).LaG = G.La K L0.sc ∧ (H.L K Cr Λ).lenMN = Λ.len ∧ (H.L K Cr Λ).F = Fval L0 ∧
    (H.Gx K Cr Λ).bs = bsA ∧ (H.Gx K Cr Λ).off = offW L0 ∧ (H.Gx K Cr Λ).kapI = kapI ∧
    (H.Gx K Cr Λ).ep = ep :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end TieHyp

theorem bsC_natCast_val (N : ℕ) [NeZero N] (h t : ℕ) :
    (bsC (h : ZMod N) (t : ZMod N)).val = bsVal N (h % N) (t % N) := by
  rw [bsC_val, ZMod.val_natCast, ZMod.val_natCast]

open Classical in

def offShd (R : Ranks) (TTn : Finset ℕ) (sc : Scale) (offS : ℕ → ℕ → ℝ) (j t : ℕ) : ℝ :=
  if j ∈ Finset.Icc 1 R.m then offS j (t % R.n)
  else if t % R.n ∈ TTn then sc.b' / sc.x else sc.w'' R.n

theorem mem_TT_iff_image {D : D7} (t : G.HH D) : t ∈ D.host.TT ↔ t.val ∈ D.host.TT.image Formalism.HC.Frame.A.val := by
  constructor
  · exact fun h => Finset.mem_image_of_mem _ h
  · intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    exact (Formalism.HC.Frame.A.val_injective _ hst) ▸ hs

theorem offW_false_shd {D : D7} (L : SizeData₂ D) (offS : ℕ → ℕ → ℝ)
    (hS : ∀ j ∈ SizeData₂.lifts D, ∀ t : G.HH D, wj D j (tauOf D (false, t)) - (G.bL L t : ℝ) = offS j t.val)
    (j t : ℕ) :
    offW L j (false, D.R.ofNat t) = offShd D.R (D.host.TT.image Formalism.HC.Frame.A.val) L.sc offS j t := by
  unfold offW offShd
  have hv : (D.R.ofNat t).val = t % D.R.n := D.R.val_ofNat t
  by_cases hj : j ∈ SizeData₂.lifts D
  · have hj' : j ∈ Finset.Icc 1 D.R.m := hj
    rw [if_pos hj, if_pos hj', ← hv, ← hS j hj]
    by_cases h : (D.R.ofNat t) ∈ D.host.TT
    · rw [if_pos ⟨rfl, h⟩]
    · rw [if_neg (fun h' => h h'.2)]
      have e : G.bL L (D.R.ofNat t) = 0 := by unfold G.bL; rw [dif_neg h]
      rw [e, Int.cast_zero]
  · have hj' : j ∉ Finset.Icc 1 D.R.m := hj
    rw [if_neg hj, if_neg hj']
    unfold offC
    have h2 : ¬ G.IsThickPl D (false, (D.R.ofNat t)) := fun h => Bool.noConfusion h.1
    rw [if_neg h2, ← hv]
    by_cases h : (D.R.ofNat t) ∈ D.host.TT
    · rw [if_pos (show G.IsTopPl D (false, (D.R.ofNat t)) from ⟨rfl, h⟩), if_pos ((mem_TT_iff_image _).1 h)]
    · rw [if_neg (fun h' : G.IsTopPl D (false, (D.R.ofNat t)) => h h'.2),
        if_neg (fun h' => h ((mem_TT_iff_image _).2 h'))]

theorem allOf_instW_eq {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (kapI : KapI) (ep : ℕ → ℕ)
    (hR : D.R = D'.R) (hTT : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val)
    (hT2 : D.host.T2 = D'.host.T2) (hu0 : D.host.u0.val = D'.host.u0.val)
    (hcls : D.host.cls = D'.host.cls)
    (hhP : ∀ p, (G.hP D p).val = (G.hP D' p).val)
    (hsc : L.sc = L'.sc) (hSc : L.Sc = L'.Sc) (heta : L.etaSz = L'.etaSz)
    (haT : ∀ (t : D.host.TT) (t' : D'.host.TT), (t : D.R.A).val = (t' : D'.R.A).val →
      L.aT t = L'.aT t')
    (hbT : ∀ (t : D.host.TT) (t' : D'.host.TT), (t : D.R.A).val = (t' : D'.R.A).val →
      L.bT t = L'.bT t')
    (hwj : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c (t : G.HH D) (t' : G.HH D'), t.val = t'.val →
      wj D j (tauOf D (c, t)) = wj D' j (tauOf D' (c, t'))) :
    allOf (instW L kapI ep) = allOf (instW L' kapI ep) := by
  refine allOf_eq _ _ hR hTT hT2 hu0 hcls hhP hsc hSc heta ?_ ?_ rfl rfl haT hbT
  · intro h t h' t' hh ht
    exact bsA_val_eq (congrArg Ranks.toFrame hR) h t h' t' hh ht
  · intro j c t t' ht
    cases c
    · refine offW_false_eq L L' hR hTT hsc j t t' ht (fun h1 h2 => ?_)
      rw [hwj j h1 h2 false t t' ht]
      have e : G.bL L t = G.bL L' t' := extension_by_zero_val_eq (congrArg Ranks.toFrame hR) hTT _ _ hbT t t' ht
      rw [e]
    · exact offW_true_eq L L' hR hTT hT2 hu0 hsc j t t' ht (fun h1 h2 => hwj j h1 h2 true t t' ht)

theorem tieHyp_sameButT {D D' : D7} {gatT : GatTies D} {gatT' : GatTies D'} {L0 : SizeData₂ D} {L0' : SizeData₂ D'}
    {kapI : KapI} {ep : ℕ → ℕ} (H : TieHyp gatT L0 kapI ep) (H' : TieHyp gatT' L0' kapI ep) (K : G.Consts) (Cr : ℝ)
    (Λ : LatIn D) (Λ' : LatIn D') (hA : allOf (instW L0 kapI ep) = allOf (instW L0' kapI ep)) :
    (∀ (t : D.host.TT) (t' : D'.host.TT), (t : D.R.A).val = (t' : D'.R.A).val →
      ∀ j p e, (H.L K Cr Λ).wPart j t p e = (H'.L K Cr Λ').wPart j t' p e) ∧
    ∀ p : ℕ, p.Prime → gainTot (H.L K Cr Λ) p = gainTot (H'.L K Cr Λ') p ∧ ioTot (H.L K Cr Λ) p = ioTot (H'.L K Cr Λ') p ∧
      ((p : ℝ) ≤ L0'.sc.X'' D'.R.n → TTwVals (H.L K Cr Λ) p = TTwVals (H'.L K Cr Λ') p) := by
  have h := tie_invariance L0 L0' (instW L0 kapI ep) (instW L0' kapI ep) K
    {p | NoGain (instW L0 kapI ep) K Cr p} {p | NoGain (instW L0' kapI ep) K Cr p}
    Λ.len Λ'.len H.hw H'.hw H.hg H'.hg H.hu H'.hu hA
  have hX : L0.sc.X'' D.R.n = L0'.sc.X'' D'.R.n := congrArg GAll.Xpp hA
  refine ⟨h.1, fun p hp => ⟨(h.2 p hp).1, (h.2 p hp).2.1, fun hle => (h.2 p hp).2.2 ?_⟩⟩
  exact ⟨fun _ => Or.inl hle, fun _ => Or.inl (hX ▸ hle)⟩

end Formalism.MainNotions.Inhab

end
