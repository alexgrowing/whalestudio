import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.NotPtIntZeroTarget
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

noncomputable section

namespace GlobalTheory.LvT.BuiltChain

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

section General

variable {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] (emb : ι → E →+* K)

omit [Fintype ι] in

theorem mem_dualFr_tauLat {n : ℕ} (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)) (φ : Fin n → K) :
    φ ∈ dualFr (tauLat emb τ L) ↔ ∀ y ∈ L, φ ⬝ᵥ (fun a => emb τ (y a)) ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro h y hy
    exact h _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨y, hy, rfl⟩ := hz; exact h y hy
    | zero => simp
    | add y z _ _ hy hz => rw [dotProduct_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [dotProduct_smul]; exact Submodule.smul_mem _ c hy

omit [Fintype ι] in

theorem dualFr_tauLat_sum {N n : ℕ} (hN : N = n + 1) (τ : ι) {t : E} (ht : t ≠ 0) (L : Submodule (𝓞 E) (Fin N → E))
    (L' : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) :
    dualFr (tauLat emb τ L) = Br.sumLat hN (dualFr (tauLat emb τ L')) (emb τ t) := by
  subst hN
  ext φ
  rw [mem_dualFr_tauLat]
  change _ ↔ (fun a : Fin n => φ a.castSucc) ∈ dualFr (tauLat emb τ L') ∧ ∃ c : 𝓞 K, φ (Fin.last n) = (c : K) * emb τ t
  replace hL : ∀ x, x ∈ L ↔ (fun a : Fin n => x a.castSucc) ∈ L' ∧ t * x (Fin.last n) ∈ (1 : Submodule (𝓞 E) E) := hL
  rw [mem_dualFr_tauLat]
  have e : ∀ y : Fin (n + 1) → E, φ ⬝ᵥ (fun a => emb τ (y a)) =
      (fun a : Fin n => φ a.castSucc) ⬝ᵥ (fun a => emb τ (y a.castSucc)) + φ (Fin.last n) * emb τ (y (Fin.last n)) := by
    intro y
    simp only [dotProduct, Fin.sum_univ_castSucc]
  have ht' : emb τ t ≠ 0 := (map_ne_zero _).2 ht
  constructor
  · intro h
    refine ⟨fun y hy => ?_, ?_⟩
    · have := h (Fin.snoc y 0) ((hL _).2 ⟨by simpa using hy, by simp⟩)
      rw [e] at this
      simpa using this
    · have := h (Fin.snoc (0 : Fin n → E) t⁻¹) ((hL _).2 ⟨by simp only [Fin.snoc_castSucc]; exact L'.zero_mem, by
        rw [Fin.snoc_last, mul_inv_cancel₀ ht]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩)
      rw [e] at this
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, map_zero] at this
      have h0 : (fun a : Fin n => φ a.castSucc) ⬝ᵥ (fun _ => (0 : K)) = 0 := dotProduct_zero _
      rw [h0, zero_add, map_inv₀] at this
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
      refine ⟨c, ?_⟩
      change _ = algebraMap (𝓞 K) K c * _
      rw [hc, inv_mul_cancel_right₀ ht']
  · rintro ⟨h1, c, hc⟩ y hy
    obtain ⟨h2, h3⟩ := (hL y).1 hy
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h3
    rw [e]
    refine Submodule.add_mem _ (h1 _ h2) ?_
    rw [hc, mul_assoc, ← map_mul, ← hr]
    exact Submodule.mem_one.2 ⟨c * RingOfIntegers.mapRingHom (emb τ) r, by rw [map_mul]; rfl⟩

omit [NumberField E] [NumberField K] [Fintype ι] in

theorem invTrK_embGL_apply {n : ℕ} (γ : GL (Fin n) E) (τ : ι) (a b : Fin n) :
    ((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      emb τ (((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) b a) := by
  simp only [invTrK, inside₂, embGL, Formalism.UG.bc, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.pi_apply,
    transpose_apply, ← map_inv]
  rfl

omit [NumberField E] in

theorem brAt_rhoVr {N n : ℕ} (hN : N = n + 1) {lam : ι → DomWeight N} {sg : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (t : ι → K)
    (γ : GL (Fin n) E) (γ' : GL (Fin N) E)
    (h1 : ∀ x, iniH hN (((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) =
      ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x)
    (h2 : ∀ x, (((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) (G : Formalism.L2.DIV.VV K lam) :
    Br.brAt hN lam sg t (rhoVr emb lam γ' G) = rhoVr emb sg γ (Br.brAt hN lam sg t G) := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  have key := GlobalTheory.BranchFormula.equivariance K ι N n hN lam sg hI hS (invTrK (embGL emb γ)) (invTrK (embGL emb γ'))
    (fun τ => by
      simp only [invTrK_embGL_apply]
      refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
      · have h := congrFun (h1 (Pi.single (Br.iC hN a) 1)) b
        have e : iniH hN (Pi.single (Br.iC hN a) (1 : E)) = Pi.single a 1 := by
          funext i
          simp only [iniH, Pi.single_apply, (Br.iC_inj hN).eq_iff]
        rw [e, mulVec_single_one, mulVec_single_one] at h
        exact congrArg _ h
      · have h := h2 (Pi.single (Br.iC hN a) 1)
        rw [mulVec_single_one, Pi.single_eq_of_ne (hne a).symm] at h
        exact (congrArg _ h).trans (map_zero _)
      · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
        have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
        rw [e, mulVec_zero, mulVec_single_one] at h
        exact (congrArg _ h).trans (map_zero _)
      · have h := h2 (Pi.single (Br.iL hN) 1)
        rw [mulVec_single_one, Pi.single_eq_same] at h
        exact (congrArg _ h).trans (map_one _)) G
  rw [Br.brAt, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  exact congrArg _ key

variable [StarRing E] [StarRing K] (σ : K →+* ℂ)

theorem evV_rho {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (b : S.β) (g : S.G b) (v : Formalism.L2.DIV.VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

omit [NumberField E] [NumberField K] [StarRing E] [StarRing K] in

theorem polOf_evV {n : ℕ} (lam : ι → DomWeight n) (v : Formalism.L2.DIV.VV K lam) :
    polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) =
      MvPolynomial.map σ v.1 := by
  have h := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (MvPolynomial.map σ v.1)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  rwa [e] at h

variable {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hc : ι → HCParam R)

omit [StarRing E] [StarRing K] in

theorem br_map (v : Formalism.L2.DIV.VV K (lamT hc R.m)) :
    Q.br emb σ hc (MvPolynomial.map σ v.1) =
      MvPolynomial.map σ (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz) v).1 := by
  simp only [PerIn.br, Br.brAt, Br.brStd, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_smul, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_prod σ]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (map_zpow₀ σ _ _).symm

theorem rho_mv_mem {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (x : S.FormsK emb lam h)
    (hx : x ∈ (S.hlat emb lam h).L) (b : S.β) (d : S.D b) :
    S.rho emb lam b (S.mv b d) (x.1 (S.cl b d)) ∈ delAtr emb lam (S.Lsh b d) := by
  have h1 : delAtr emb lam (S.Lsh b (S.mv b d • S.rep (S.cl b d))) =
      (delAtr emb lam (S.Lsh b (S.rep (S.cl b d)))).map ((S.rho emb lam b (S.mv b d)).restrictScalars (𝓞 K)) :=
    (h b).del_smul (S.mv b d) (S.rep (S.cl b d))
  rw [S.mv_smul] at h1
  rw [h1]
  exact Submodule.mem_map_of_mem (hx (S.cl b d))

theorem exists_image (h6 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6) (hI : I.Ok) (hQ : Q.Ok)
    (hW : ∀ τ, Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ)) (hS : ∀ τ, Br.SameShift (lamT hc R.m τ) (Q.sgT τ))
    (hF : ((I.S R.m).fam emb (lamT hc R.m)).Ok) (hP : (Q.S'.fam emb Q.sgT).Ok)
    (x : (I.S R.m).FormsK emb (lamT hc R.m) hF) (hx : x ∈ ((I.S R.m).hlat emb (lamT hc R.m) hF).L) :
    ∃ y ∈ (Q.S'.hlat emb Q.sgT hP).L, Q.S'.embF emb σ Q.sgT hP y =
      (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz ((I.S R.m).embF emb σ (lamT hc R.m) hF x)) := by
  let v : Q.S'.Cl → Formalism.L2.DIV.VV K (lamT hc R.m) := fun c =>
    (I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c))
  let B := Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
  refine ⟨⟨fun c => B (v c), fun c g => ?_⟩, fun c => ?_, funext fun c => ?_⟩
  · have h1 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 g.1 *
        (I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c)) = x.1 (Q.tilC c) := x.2 (Q.tilC c) (Q.stabMap hQ c g)
    have h2 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (Q.ext c.1 g.1) (v c) = v c := by
      have h3 := congrArg ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))) h1
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
      exact h3
    show ((Q.S'.chr c.1 g.1 : Kˣ) : K) • rhoVr emb Q.sgT (Q.S'.gam c.1 g.1) (B (v c)) = B (v c)
    rw [← brAt_rhoVr emb (N_m_succ R) hW hS _ (Q.S'.gam c.1 g.1) ((I.S R.m).gam Q.b0 (Q.ext c.1 g.1))
      (fun z => by rw [← map_inv, ← map_inv, ← map_inv]; exact hQ.gam_ini _ _ z)
      (fun z => by rw [← map_inv, ← map_inv]; exact hQ.gam_last _ _ z), ← map_smul, ← hQ.chr_ext]
    exact congrArg B h2
  · have h2 : v c ∈ delAtr emb (lamT hc R.m) ((I.S R.m).Lsh Q.b0 (Q.til c.1 (Q.S'.rep c))) :=
      rho_mv_mem emb (I.S R.m) (lamT hc R.m) hF x hx Q.b0 (Q.tilPt c)
    refine GlobalTheory.BranchFormula.integrality h6 K ι _ _ (N_m_succ R) _ _ hW hS _ _ (fun τ => (map_ne_zero _).2 hQ.tz_ne) _ ?_
    unfold delAtr at h2
    rwa [funext fun τ => dualFr_tauLat_sum emb (N_m_succ R) τ hQ.tz_ne _ _ (hQ.Lsh_til c.1 (Q.S'.rep c))] at h2
  · show _ = fnOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) 1 (Q.br emb σ hc
      (polOf (Gr emb σ (R.N R.m)) (shiftOf (lamT hc R.m)) (fr0 emb σ (R.N R.m))
        ((I.S R.m).tr emb σ Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
          (evV emb (1 : Matrix (Fin (R.N R.m)) (Fin (R.N R.m)) E) (lamT hc R.m) σ (x.1 (Q.tilC c))))))
    rw [← evV_rho, polOf_evV, br_map]
    rfl

omit [StarRing K] in

theorem weights_ok (emb : ι → E →+* K) [StarRing K] (h : ∀ τ, Q.sg τ = (RowPar.of (hc τ)).sg) (τ : ι) :
    Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ) ∧ Br.SameShift (lamT hc R.m τ) (Q.sgT τ) := by
  classical
  let X : Fields := { F := ℚ, E := E, K := K, Tau := ι, emb := emb }
  let W : Wts X Unit R := ⟨fun τ => RowPar.of (hc τ), fun _ => hc, ∅⟩
  have := GlobalTheory.BranchMembers.members X Unit R W
    ⟨fun τ => ⟨hc τ, rfl⟩, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩ () τ
  unfold PerIn.sgT
  rw [h τ]
  exact this

end General

variable {D : D7} {u : D.what₂.Word}

def IsBuilt (X : Ch D u) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : StarRing E) (emb : D.what₂.Tau → E →+* D.what₂.LL)
    (I : ChainIn E D.what₂.LL D.what₂.Tau D.R) (J : AtIn I) (Q : PerIn I) (Z : FmIn J D.what₂.places)
    (hI : I.Ok) (hJ : J.Ok) (hQ : Q.Ok) (l : J.Laws emb D.what₂.embLL (D.hcW u))
    (lf : FmLaws J Q emb D.what₂.embLL (D.hcW u) D.what₂.places hI hQ) (hT : Q.Over J),
    (∀ τ, Q.sg τ = (RowPar.of (D.hcW u τ)).sg) ∧
      X = ⟨_, _, _, forms J Q emb D.what₂.embLL (D.hcW u) Z hI hJ hQ l lf hT⟩

theorem ptInt_of_isBuilt (h6 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6) {X : Ch D u} (hX : IsBuilt X) : PtInt X := by
  obtain ⟨E, _, _, _, emb, I, J, Q, Z, hI, hJ, hQ, l, lf, hT, hsg, rfl⟩ := hX
  refine (PtIntTest.ptInt_iff _).2 fun x hx => ?_
  exact exists_image emb D.what₂.embLL Q (D.hcW u) h6 hI hQ (fun τ => (weights_ok Q _ emb hsg τ).1)
    (fun τ => (weights_ok Q _ emb hsg τ).2) (lf.fam _) lf.famP x hx

theorem ptInt_tw (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (hX : IsBuilt (tw Tw u μ))
    (h6 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6) : PtInt (tw Tw u μ) :=
  ptInt_of_isBuilt h6 hX

end GlobalTheory.LvT.BuiltChain
