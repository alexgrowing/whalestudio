import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NearPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLifts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeInvOfPosDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeMulOfBoth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.NearWd

theorem congE_of_cols {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (c : ℕ)
    (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (h : ∀ j l : Fin n, IntAt P ((((qOf P : ℕ) : E) ^ c)⁻¹ * ((g⁻¹ * g') (Pi.single j (1 : E)) l - (Pi.single j (1 : E) : Sp E n) l))) :
    CongE P c g' g := by
  intro x hx
  have e1 : g (g⁻¹ (g' x)) = g' x := by
    show (g * g⁻¹) (g' x) = g' x
    rw [mul_inv_cancel]; rfl
  have e : (((qOf P : ℕ) : E) ^ c)⁻¹ • (g' x - g x) = g ((((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x)) := by
    rw [map_smul, map_sub]
    show _ = _ • (g (g⁻¹ (g' x)) - g x)
    rw [e1]
  rw [e]
  refine (hg _).2 ?_
  rw [stdAt, mem_localization_standardLattice] at hx ⊢
  intro l
  have hs := GlobalTheory.TopStep.apply_eq_sum ((g⁻¹ * g').toLinearMap - LinearMap.id) x l
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, Pi.sub_apply] at hs
  rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hs, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun a b ha hb => ha.add hb) (by simpa using GlobalTheory.TopInv.intAt_nat (P := P) 0) fun j _ => ?_
  rw [mul_left_comm]
  exact (hx j).mul (h j l)

theorem congAt_of_near_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (k k' : GL (Fin N) E)
    (h : GlobalTheory.TwU.NearAt Q n y k) (h' : GlobalTheory.TwU.NearAt Q n y k') : GlobalTheory.TwU.CongAt Q n (GlobalTheory.TwU.ratA F (k⁻¹ * k')) := by
  have e : GlobalTheory.TwU.ratA F (k⁻¹ * k') = (y⁻¹ * GlobalTheory.TwU.ratA F k)⁻¹ * (y⁻¹ * GlobalTheory.TwU.ratA F k') := by
    rw [map_mul, map_inv]; group
  rw [e]
  exact GlobalTheory.CongProd.congAt_mul_prod _ _ _ _ _ _ _ (GlobalTheory.TwU.congAt_inv_pos_depth _ _ _ _ _ _ hn h) h'

theorem val_eq_of_congE {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (j : ℕ) (hj : j < B.R.m) (b : (I.idx a).β j)
    (P : SBof I a) (g g' : Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N j)) (z z' : B.fields.K)
    (hz : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j b P) g z)
    (hz' : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j b P) g' z')
    (hgg : CongE P.1 ((I.cst a).D P) g' g) : z = z' := by
  classical
  have hL := hOk.idx_ok a
  obtain ⟨r, hr, hrx, rfl⟩ := hz
  obtain ⟨r', hr', hrx', rfl⟩ := hz'
  have hgC : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp j P.1 ((I.idx a).h j b P) := ⟨r, hr, hrx⟩
  have hgI : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1 := hL.int j b P hgC
  let G : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1) := ⟨g, hgI⟩
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hred : ∀ x ∈ stdAt B.fields.E (B.R.N j) P.1, redV P.1 (g x) = (GlobalTheory.TopStep.redGL _ P.1 G).1.mulVec (redV P.1 x) :=
      fun x hx => GlobalTheory.TopStep.redV_redGL G hx
    have hmem : GlobalTheory.TopStep.redGL _ P.1 G ∈ ((I.idx a).levG j b ⟨P.1, hP⟩).H :=
      (hL.grpG j b ⟨P.1, hP⟩ _).2 ⟨g, hgC, hred⟩
    have hκ : (GlobalTheory.TopStep.redGL _ P.1 G)⁻¹ ∈ ((I.idx a).levG j b ⟨P.1, hP⟩).H := inv_mem hmem
    have hred' : ∀ x ∈ stdAt B.fields.E (B.R.N j) P.1, redV P.1 (g x) = (((GlobalTheory.TopStep.redGL _ P.1 G)⁻¹)⁻¹).1.mulVec (redV P.1 x) := by
      intro x hx
      rw [inv_inv]
      exact hred x hx
    rw [chiInv_at_type I hOk a j b P hP g g r hr hrx _ hκ hred' (congE_refl _ _ _),
      chiInv_at_type I hOk a j b P hP g' g r' hr' hrx' _ hκ hred' hgg]
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
    have hH : G ∈ ((I.idx a).levQ j b ⟨P.1, hQ⟩).H := by
      rw [hL.grpQ j b ⟨P.1, hQ⟩]
      exact Subgroup.mem_subgroupOf.2 hgC
    have hg1 : g = ((G⁻¹)⁻¹).1 := by rw [inv_inv]
    rw [chiInv_at_twist I hOk a j hj b P hQ g g r hr hrx G⁻¹ (inv_mem hH) hg1 (congE_refl _ _ _),
      chiInv_at_twist I hOk a j hj b P hQ g' g r' hr' hrx' G⁻¹ (inv_mem hH) hg1 hgg]

end GlobalTheory.Mem.Col2.QChi.NearWd

namespace GlobalTheory.Mem.Col2.QChi

theorem nearPair_val_unique : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a)
    (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))
    (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K),
    GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g z → GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g' z' → z = z' := by
  intro B X I hOk l Z a v P x g g' z z' h h'
  have hL := hOk.idx_ok a
  have hm := hL.hm
  have key : ∀ j, j = B.R.m - 2 + 1 → ∃ b : (I.idx a).β j, (I.idx a).h j b P = 1 := by
    rintro j rfl
    obtain ⟨b, -⟩ := hL.last_uniq
    exact ⟨b, hL.last_h b P⟩
  obtain ⟨b, hb⟩ := key (B.R.m - 1) (by omega)
  obtain ⟨hz, hn⟩ := h
  obtain ⟨hz', hn'⟩ := h'
  rw [← hb] at hz hz'
  have hD : 1 ≤ (I.cst a).D P := hL.cst_ok.D_pos P
  unfold NearV at hn hn'
  have hc := NearWd.congAt_of_near_same _ _ hD _ _ _ hn hn'
  have hgI : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 :=
    hL.int _ b P ((GlobalTheory.TwU.exists_midLev_iff _ _ _ _ _ _ _ g).1 ⟨z, hz⟩)
  exact NearWd.val_eq_of_congE I hOk a (B.R.m - 1) (by omega) b P g g' z z' hz hz'
    (NearWd.congE_of_cols P.1 _ g g' hgI (GlobalTheory.LevFrame.cols_of_congAt (sm I l Z) P.1 _ (g⁻¹ * g') (by rw [map_mul, map_inv]; exact hc)))

end GlobalTheory.Mem.Col2.QChi

end
