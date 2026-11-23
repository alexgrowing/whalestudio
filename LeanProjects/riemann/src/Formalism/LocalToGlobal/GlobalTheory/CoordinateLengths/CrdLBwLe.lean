import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.IsCrdExists
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable {D : D7} {u : D.what₂.Word}

theorem crd_Bw (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (hB' : ∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c))
    (x : ((D.fm u).lat 0).V) (hx : x ∈ (D.fm u).Bw 0 w v) (c : (D.mem u).C.cls 0) :
    crd T B x c ∈ ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift)) := by
  obtain ⟨P, hP, hPe⟩ := (T.bw0 w hw hs v x).1 hx c (B c) (B' c) (hB c) (hB' c)
  have hc : IsCrd T (B c) x c (MvPolynomial.C (∏ τ, (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ).det ^
      shiftOf (lamT u 0) τ) * Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c)) P) := by
    intro z
    rw [hPe z, ← bwA_N_mul, fnOf_mul]
  rw [crd_eq T B hc]
  have ho : ∀ τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ = 1 := by
    intro τ h
    unfold bwA_N
    rw [if_neg h]
  have hprod : ∏ τ, (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ).det ^ shiftOf (lamT u 0) τ =
      (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
        ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift := by
    rw [Fintype.prod_eq_single ((D.fm u).tauOf w v) (fun τ h => by rw [ho τ h, Matrix.det_one, one_zpow]), lamT_zero]
    rfl
  rw [hprod, MvPolynomial.C_mul']
  exact ⟨_, ⟨P, Submodule.subset_span hP, rfl⟩, rfl⟩

theorem crd_S (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (x : ((D.fm u).lat 0).V) (hx : x ∈ (D.fm u).S 0 w) (c : (D.mem u).C.cls 0) :
    crd T B x c ∈ intSubm D w ((D.fm u).lam 0) := by
  have hB'' : IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) (B c) := by
    rw [← bwG_Ld_coe D u 0 (Nat.zero_le _) c]
    have hw' : D.what₂.places.resChar w = (D.mem u).A.T := hw
    rw [hw']
    exact hB c
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨P, hP, hPe⟩ := (T.val0.lat y).1 hy w c (B c) hB''
    rw [crd_eq T B (c := c) hPe]
    exact Submodule.subset_span hP
  | zero =>
    rw [show crd T B 0 c = 0 from congrFun (map_zero (crdL T B w)) c]
    exact Submodule.zero_mem _
  | add y y' _ _ hy hy' =>
    rw [show crd T B (y + y') c = crd T B y c + crd T B y' c from congrFun (crd_add T B y y') c]
    exact Submodule.add_mem _ hy hy'
  | smul r y _ hy =>
    rw [show crd T B (r • y) c = crd T B ((r : D.what₂.LL) • y) c from rfl, crd_smul T B (r : D.what₂.LL) y c]
    exact Submodule.smul_mem _ (⟨D.what₂.embLL (r : D.what₂.LL), ⟨r, r.2, rfl⟩⟩ : bwA_Ow D w) hy

theorem crd_tL (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) (b : ℤ)
    (y : ((D.fm u).lat 0).V) (hy : y ∈ tL D u w b ((D.fm u).S 0 w)) (c : (D.mem u).C.cls 0) :
    crd T B y c ∈ (intSubm D w ((D.fm u).lam 0)).map (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ b)) := by
  obtain ⟨x, hx, hxy⟩ := hy
  have hc : IsCrd T (B c) y c ((((D.mem u).A.T : ℂ) ^ b) • crd T B x c) := by
    intro z
    rw [hxy, map_smul]
    show (((D.mem u).A.T : ℂ) ^ b) * (D.fm u).emb 0 x c z = _
    rw [crd_spec T B x c z]
    rfl
  rw [crd_eq T B hc]
  exact ⟨_, crd_S T w hw B hB x hx c, rfl⟩

theorem crdL_Bw_le (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (hB' : ∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c)) :
    ((D.fm u).Bw 0 w v).map (crdL T B w) ≤ Submodule.pi Set.univ fun c =>
      ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_pi]
  intro c _
  exact crd_Bw T w hw hs v B B' hB hB' x hx c

theorem crdL_tL_le (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) (b : ℤ) :
    (tL D u w b ((D.fm u).S 0 w)).map (crdL T B w) ≤ Submodule.pi Set.univ fun _ =>
      (intSubm D w ((D.fm u).lam 0)).map (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ b)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap, Submodule.mem_pi]
  intro c _
  exact crd_tL T w hw B hB b y hy c

end Formalism.L2.GlobalTheoryTheory.LemB
