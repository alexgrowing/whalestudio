import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem homRe_rfl {E : Type} [Field E] {a b : ℕ} (x : Formalism.L2.Col.HomE E a b) : homRe (rfl : a = a) (rfl : b = b) x = x := by
  apply LinearMap.ext
  intro v
  funext i
  simp [homRe]

theorem reV_rfl {D : D7} {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) : reV (rfl : a = a) (rfl : b = b) G = G := by
  funext z
  simp [reV]

theorem inFr_symm_inFr {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a) (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (x : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' x) = x := by
  apply LinearMap.ext
  intro v
  simp [Formalism.L2.Col.inFr]

theorem kerTh_homRe {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)} {M' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)}
    {L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N)} {L' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N')}
    (hM : HEq M L) (hM' : HEq M' L') (Ξ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) :
    kerTh B χ SS c M M' (fun x => Ξ (homRe ha hb x)) = reV ha hb (kerTh B χ SS c L L' Ξ) := by
  subst ha hb
  cases eq_of_heq hM
  cases eq_of_heq hM'
  simp only [homRe_rfl, reV_rfl]

set_option maxHeartbeats 1000000 in

theorem kerTh_pair_eq : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)), ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') = reV hr hr' (kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D j (Nat.le_of_succ_le hj)) J.a (J.pt std j (Nat.le_of_succ_le hj) La).1 ((J.St j (Nat.le_of_succ_le hj)).K (J.chart std j (Nat.le_of_succ_le hj) La)).lev.Lb) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La').1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La')).lev.Lb) (S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La')))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj hr hr' La La' hLa hLa'
  obtain ⟨-, -, h1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨-, -, h2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun x =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe hr hr' x) := by
    funext x
    simp only [xiM, movD, Joint.xi0]
    rw [dif_pos ⟨hj, hr, hr'⟩, inFr_symm_inFr]
  rw [hx]
  exact kerTh_homRe _ _ _ _ hr hr' h1 h2 _

end GlobalTheory.TwV.DelB

end
