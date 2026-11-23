import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf

noncomputable section

namespace GlobalTheory.Mem.Col2.KerRat

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem sum_cover {K M G D G' D' : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] [MulAction G D] [Group G']
    [MulAction G' D'] [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient G' D')]
    (π : D → D') (hs : Function.Surjective π) (h1 : ∀ (g : G) d, ∃ g' : G', π (g • d) = g' • π d)
    (h2 : ∀ (g' : G') d e, g' • π d = π e → ∃ g : G, g • d = e)
    (h3 : ∀ d, Nat.card (MulAction.stabilizer G d) = Nat.card (MulAction.stabilizer G' (π d)))
    (r : MulAction.orbitRel.Quotient G D → D) (hr : ∀ q, Quotient.mk (MulAction.orbitRel G D) (r q) = q)
    (r' : MulAction.orbitRel.Quotient G' D' → D') (hr' : ∀ q, Quotient.mk (MulAction.orbitRel G' D') (r' q) = q)
    (f : D' → M) (hf : ∀ (g' : G') d, f (g' • d) = f d) :
    ∑ q, ((Nat.card (MulAction.stabilizer G (r q)) : ℕ) : K)⁻¹ • f (π (r q)) =
      ∑ q, ((Nat.card (MulAction.stabilizer G' (r' q)) : ℕ) : K)⁻¹ • f (r' q) := by
  refine Fintype.sum_bijective (fun q => Quotient.mk (MulAction.orbitRel G' D') (π (r q))) ⟨fun q q' h => ?_, fun q' => ?_⟩ _ _
    fun q => ?_
  · obtain ⟨g', hg⟩ : ∃ g' : G', g' • π (r q') = π (r q) := Quotient.exact h
    obtain ⟨g, hg⟩ := h2 g' _ _ hg
    rw [← hr q, ← hr q']
    exact Quotient.sound ⟨g, hg⟩
  · obtain ⟨d, hd⟩ := hs (r' q')
    refine ⟨Quotient.mk _ d, ?_⟩
    obtain ⟨g, hg⟩ : ∃ g : G, g • d = r (Quotient.mk _ d) := Quotient.exact (hr (Quotient.mk _ d))
    obtain ⟨g', hg'⟩ := h1 g d
    rw [← hr' q', ← hd]
    exact Quotient.sound ⟨g', by rw [← hg, hg']⟩
  · obtain ⟨g', hg⟩ : ∃ g' : G', g' • π (r q) = r' (Quotient.mk _ (π (r q))) := Quotient.exact (hr' (Quotient.mk _ (π (r q))))
    rw [← hg, hf, h3, Nat.card_congr (MulAction.stabilizerEquivStabilizer (G := G') (a := π (r q)) (b := g' • π (r q)) (g := g') rfl).toEquiv]

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  (I : ChainIn E K ι R) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R) (hI : I.Ok)

abbrev PtKer : Type := ∀ i b b', (I.S i).D b → (I.S (i + 1)).D b' → (VV K (lamT hc i) →ₗ[K] VV K (lamT hc (i + 1)))

abbrev ev (i : ℕ) : VV K (lamT hc i) →ₛₗ[σ] (Fr emb σ (R.N i) → ℂ) :=
  evV emb (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) E) (lamT hc i) σ

variable {I hc} (k : PtKer I hc)

def EqTarget (i : ℕ) : Prop := ∀ b b' (g' : (I.S (i + 1)).G b') d d',
  k i b b' d (g' • d') = (I.S (i + 1)).rho emb (lamT hc (i + 1)) b' g' ∘ₗ k i b b' d d'

def ReadsAt (i : ℕ) : Prop := ∀ c c' F, (I.chain emb σ hI hc).Kmap i c c' (ev emb σ hc i F) =
  ev emb σ hc (i + 1) (k i c.1 c'.1 ((I.S i).rep c) ((I.S (i + 1)).rep c') F)

def stepPt (i : ℕ) (x : (I.S i).Cl → VV K (lamT hc i)) (b' : (I.S (i + 1)).β) (d' : (I.S (i + 1)).D b') : VV K (lamT hc (i + 1)) :=
  letI := I.clFin hI i
  ∑ c : (I.S i).Cl, ((Nat.card ((I.S i).Stab c) : ℕ) : K)⁻¹ • k i c.1 b' ((I.S i).rep c) d' (x c)

def colPt (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) (j : ℕ) : ∀ b, (I.S j).D b → VV K (lamT hc j) :=
  Nat.rec (motive := fun j => ∀ b, (I.S j).D b → VV K (lamT hc j)) φ
    (fun j ψ => stepPt hI k j fun c => ψ c.1 ((I.S j).rep c)) j

variable {emb k}

theorem stepPt_smul {i : ℕ} (h : EqTarget emb k i) (x : (I.S i).Cl → VV K (lamT hc i)) (b' : (I.S (i + 1)).β)
    (g' : (I.S (i + 1)).G b') (d' : (I.S (i + 1)).D b') :
    stepPt hI k i x b' (g' • d') = (I.S (i + 1)).rho emb (lamT hc (i + 1)) b' g' (stepPt hI k i x b' d') := by
  unfold stepPt
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h, map_smul]
  rfl

theorem colPt_smul (h : ∀ i, i < R.m → EqTarget emb k i) (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) {j : ℕ} (h0 : 0 < j) (hj : j ≤ R.m)
    (b : (I.S j).β) (g : (I.S j).G b) (d : (I.S j).D b) :
    colPt hI k φ j b (g • d) = (I.S j).rho emb (lamT hc j) b g (colPt hI k φ j b d) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact stepPt_smul hI (h i (by omega)) _ b g d

variable {σ hI}

theorem K_ev {i : ℕ} (h : ReadsAt emb σ hI k i) (x : (I.S i).Cl → VV K (lamT hc i)) :
    (I.chain emb σ hI hc).K i (fun c => ev emb σ hc i (x c)) =
      fun c' => ev emb σ hc (i + 1) (stepPt hI k i x c'.1 ((I.S (i + 1)).rep c')) := by
  funext c'
  unfold stepPt
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.map_smulₛₗ, map_inv₀, map_natCast, ← h]
  rfl

theorem chain_ev (h : ∀ i, i < R.m → ReadsAt emb σ hI k i) (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) {j : ℕ} (hj : j ≤ R.m) :
    letI := (I.chain emb σ hI hc).clsFin
    Formalism.ThetaLiftIndependence.chainOpM (I.chain emb σ hI hc).wt (I.chain emb σ hI hc).Kmap j (fun c => ev emb σ hc 0 (φ c.1 ((I.S 0).rep c))) =
      fun c => ev emb σ hc j (colPt hI k φ j c.1 ((I.S j).rep c)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    refine Eq.trans ?_ (K_ev (h j (by omega)) fun c => colPt hI k φ j c.1 ((I.S j).rep c))
    rw [← ih (by omega)]
    rfl

theorem exists_K_embF {i : ℕ} (h : ReadsAt emb σ hI k i) (h' : EqTarget emb k i) (hF : ((I.S i).fam emb (lamT hc i)).Ok)
    (hF' : ((I.S (i + 1)).fam emb (lamT hc (i + 1))).Ok) (x : (I.S i).FormsK emb (lamT hc i) hF) :
    ∃ y, (I.S (i + 1)).embF emb σ (lamT hc (i + 1)) hF' y = (I.chain emb σ hI hc).K i ((I.S i).embF emb σ (lamT hc i) hF x) :=
  ⟨⟨fun c' => stepPt hI k i x.1 c'.1 ((I.S (i + 1)).rep c'), fun c' g =>
    (stepPt_smul hI h' x.1 c'.1 g.1 _).symm.trans (congrArg (stepPt hI k i x.1 c'.1) g.2)⟩, (K_ev h x.1).symm⟩

variable (Q : PerIn I) (hQ : Q.Ok)

theorem lower_ev (x : (I.S R.m).Cl → VV K (lamT hc R.m)) (c : Q.S'.Cl) :
    (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz fun c => ev emb σ hc R.m (x c)) c =
      evV emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) Q.sgT σ
        (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
          ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x (Q.tilC c)))) := by
  show fnOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) 1 (Q.br emb σ hc
      (polOf (Gr emb σ (R.N R.m)) (shiftOf (lamT hc R.m)) (fr0 emb σ (R.N R.m))
        ((I.S R.m).tr emb σ Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
          (evV emb (1 : Matrix (Fin (R.N R.m)) (Fin (R.N R.m)) E) (lamT hc R.m) σ (x (Q.tilC c)))))) = _
  rw [← LvT.BuiltChain.evV_rho, LvT.BuiltChain.polOf_evV, LvT.BuiltChain.br_map]
  rfl

theorem exists_lower_embF (hW : ∀ τ, Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ))
    (hS : ∀ τ, Br.SameShift (lamT hc R.m τ) (Q.sgT τ)) (hF : ((I.S R.m).fam emb (lamT hc R.m)).Ok) (hP : (Q.S'.fam emb Q.sgT).Ok)
    (x : (I.S R.m).FormsK emb (lamT hc R.m) hF) :
    ∃ y, Q.S'.embF emb σ Q.sgT hP y =
      (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz ((I.S R.m).embF emb σ (lamT hc R.m) hF x)) := by
  let v : Q.S'.Cl → VV K (lamT hc R.m) := fun c =>
    (I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c))
  let B := Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
  refine ⟨⟨fun c => B (v c), fun c g => ?_⟩, funext fun c => (lower_ev Q hQ x.1 c).symm⟩
  have h1 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 g.1 *
      (I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c)) = x.1 (Q.tilC c) := x.2 (Q.tilC c) (Q.stabMap hQ c g)
  have h2 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (Q.ext c.1 g.1) (v c) = v c := by
    have h3 := congrArg ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))) h1
    rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
    exact h3
  show ((Q.S'.chr c.1 g.1 : Kˣ) : K) • rhoVr emb Q.sgT (Q.S'.gam c.1 g.1) (B (v c)) = B (v c)
  rw [← LvT.BuiltChain.brAt_rhoVr emb (N_m_succ R) hW hS _ (Q.S'.gam c.1 g.1) ((I.S R.m).gam Q.b0 (Q.ext c.1 g.1))
    (fun z => by rw [← map_inv, ← map_inv, ← map_inv]; exact hQ.gam_ini _ _ z)
    (fun z => by rw [← map_inv, ← map_inv]; exact hQ.gam_last _ _ z), ← map_smul, ← hQ.chr_ext]
  exact congrArg B h2

theorem ptilCol_ev (h : ∀ i, i < R.m → ReadsAt emb σ hI k i) (h' : ∀ i, i < R.m → EqTarget emb k i)
    (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) (F : Q.Mt emb σ) (y : Q.S'.Cl → VV K Q.sgT)
    (hy : ∀ c, Q.rd emb σ F c = MvPolynomial.map σ (y c).1) :
    (Q.per emb σ hI hQ hc).PtilCol (fun c => ev emb σ hc 0 (φ c.1 ((I.S 0).rep c))) F = letI := Q.clFin hQ
      σ (∑ c : Q.S'.Cl, ((Nat.card (Q.S'.Stab c) : ℕ) : K)⁻¹ • pairBK Q.sgT
        (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz) (colPt hI k φ R.m Q.b0 (Q.tilPt c))) (y c)) := by
  unfold PeriodMap.PtilCol PeriodMap.Ptil ColumnChain.col
  rw [chain_ev h φ le_rfl]
  have e := funext (lower_ev (σ := σ) (emb := emb) (hI := hI) Q hQ fun c => colPt hI k φ R.m c.1 ((I.S R.m).rep c))
  refine (congrArg (fun z => (Q.per emb σ hI hQ hc).period z F) e).trans ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
  have e2 := colPt_smul hI h' φ (lt_of_lt_of_le (by norm_num) R.two_le_m) le_rfl Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
    ((I.S R.m).rep ((I.S R.m).cl Q.b0 (Q.tilPt c)))
  rw [GStep.mv_smul] at e2
  rw [pairBK_apply, PeriodOnStep.map_pairB, ← hy, ← PeriodOnStep.polOf_evV σ emb, e2]
  rfl

end GlobalTheory.Mem.Col2.KerRat
