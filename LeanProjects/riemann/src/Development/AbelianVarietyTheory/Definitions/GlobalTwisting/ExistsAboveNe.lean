import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulMemSpan
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg

noncomputable section

namespace GlobalTheory.LvT.Built.Model

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

section Split

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def offY (y : Ys X n) : Setoid (PtY ST SG Q y) where
  r p q := SameOff ST p.1.1.deco.1.N q.1.1.deco.1.N ∧ p.1.1.deco.1.be = q.1.1.deco.1.be ∧ p.1.1.fr = q.1.1.fr ∧ p.1.2 = q.1.2
  iseqv := ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
    fun h => ⟨fun w hw => (h.1 w hw).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩,
    fun h h' => ⟨fun w hw => (h.1 w hw).trans (h'.1 w hw), h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩⟩

theorem off_mv (y : Ys X n) (p : PtY ST SG Q y) (d : DecoSet X.E n ST SG) (h1 : SameOff ST p.1.1.deco.1.N d.1.N)
    (h2 : p.1.1.deco.1.be = d.1.be) : (offY y).r p (p.mv d) := by
  classical
  by_cases h : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N
  · rw [show p.mv d = ⟨(⟨(d, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ from dif_pos h]
    exact ⟨h1, h2, rfl, rfl⟩
  · rw [show p.mv d = p from dif_neg h]

theorem ok_repl {d : Deco X.E n ST SG} (hd : d.Ok) {e : Deco X.E n ST ∅} (he : e.Ok)
    (hG : ∀ w : SG, localization₂ w.1.asIdeal d.N = localization₂ w.1.asIdeal e.N) : Deco.Ok (⟨e.N, e.f, d.be⟩ : Deco X.E n ST SG) := by
  let d0 : Deco X.E n ∅ SG := ⟨d.N, fun P => absurd P.2 (Finset.notMem_empty _), d.be⟩
  have h0 : d0.Ok := ⟨hd.lat, hd.uni, fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _),
    fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _), hd.be_add, hd.be_smul, hd.be_off,
    hd.be_surj, hd.be_ker⟩
  have h1 := GlobalTheory.GO.decoration_admissible_of_localization_eq h0 he.lat he.uni (fun P => absurd P.2 (Finset.notMem_empty _)) hG
  exact ⟨he.lat, he.uni, he.f_add, he.f_smul, he.f_off, he.f_ne, h1.be_add, h1.be_smul, h1.be_off, h1.be_surj, h1.be_ker⟩

theorem exists_uf (γ : GL (Fin n) X.E) (h : (γ : Matrix (Fin n) (Fin n) X.E)ᴴ * (γ : Matrix (Fin n) (Fin n) X.E) = 1) :
    ∃ g : UF X.E n, ufGL X.E n g = γ := by
  refine ⟨⟨(Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv, fun x y => ?_⟩, ?_⟩
  · show hStd X.E n (γ.1 *ᵥ x) (γ.1 *ᵥ y) = hStd X.E n x y
    have e : ∀ a b : Fin n → X.E, hStd X.E n a b = star a ⬝ᵥ b := fun _ _ => rfl
    rw [e, e, star_mulVec, dotProduct_mulVec, vecMul_vecMul, h, vecMul_one]
  · apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, LevLaws.ufGL_mulVec]
    rfl

def splitY (T : ℕ) (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG)
    (Θ : β → LevQFam X.E X.K n Q) (pref : DecoF X.E n ST SG Q → Prop) (hP : ∀ P : ST, MoveHyp ST SG P)
    (hQ : ∀ (P : ST) (w : Q), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1)
    (hy : ∀ N N', SameOff ST N N' → y.ys N = y.ys N')
    (h1 : ∀ P ∈ ST, (T : 𝓞 X.E) ∈ P.asIdeal) (h2 : ∀ P ∈ ST, (T : 𝓞 X.E) ∉ P.asIdeal ^ 2) :
    Split (tdatY ST T y β Λ Θ pref) T where
  off _ := offY y
  off_act b g d d' h := by
    refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
    · ext x
      change x ∈ localization₂ w.asIdeal (gmap g.1.1 d.1.1.deco.1.N) ↔ x ∈ localization₂ w.asIdeal (gmap g.1.1 d'.1.1.deco.1.N)
      rw [mem_localization_gmap, mem_localization_gmap, h.1 w hw]
    · change (d.1.1.deco.1.act g.1.1 g.2.1.1).be = (d'.1.1.deco.1.act g.1.1 g.2.1.1).be
      simp only [Deco.act, h.2.1]
    · funext P
      change g.1.1 * d.1.1.fr P * _ = g.1.1 * d'.1.1.fr P * _
      rw [h.2.2.1]
    · change (fun v => g.1.1 v) '' d.1.2 = (fun v => g.1.1 v) '' d'.1.2
      rw [h.2.2.2]
  off_lat _ _ _ h := h.1
  ext b d d' h e := by
    have eN : d.1.1.deco.1.N = d'.1.1.deco.1.N := (congrArg Deco.N e :)
    have ef : d.1.1.deco.1.f = d'.1.1.deco.1.f := (congrArg Deco.f e :)
    exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (Subtype.ext (Deco.ext eN ef h.2.1)) h.2.2.1)) h.2.2.2)
  surj b d e he hs := by
    refine ⟨⟨(⟨(⟨_, ok_repl d.1.1.deco.2 he fun w => hs _ fun P hP' => (hP ⟨P, hP'⟩).sg w⟩, d.1.1.fr), fun P x => ?_⟩, d.1.2), ?_⟩,
      ⟨hs, rfl, rfl, rfl⟩, Deco.ext rfl rfl (funext fun w => absurd w.2 (Finset.notMem_empty _))⟩
    · have := hs P.1 fun P' hP' => hQ ⟨P', hP'⟩ P
      change _ ∈ localization₂ P.1.asIdeal e.N ↔ _
      rw [← this]
      exact d.1.1.2 P x
    · change d.1.2 ∈ y.ys e.N
      rw [← hy _ _ hs]
      exact d.2
  off_up b d P x hx hf := by
    have e := DecoSet.up_val d.1.1.deco P (hP P) (h1 _ P.2) (h2 _ P.2) hx hf
    refine off_mv y d _ (fun w hw => ?_) (by rw [e]; rfl)
    rw [e]
    exact ((upN_spec d.1.1.deco.2.lat d.1.1.deco.2.uni P.1 (hP P).ne hx).2.2.1 w (hw _ P.2).1 (hw _ P.2).2).localization_eq.symm
  off_dn b d P g _ := by
    show (offY y).r d (d.mv (d.1.1.deco.dn P g))
    unfold DecoSet.dn
    split_ifs with h
    · exact off_mv y d _ (fun w hw =>
        ((d.1.1.deco.2.dnN_spec P (hP P).ne).2.2.1 w (hw _ P.2).1 (hw _ P.2).2).localization_eq.symm) rfl
    · exact off_mv y d _ (fun _ _ => rfl) rfl
  off_dia b d P a := off_mv y d _ (fun _ _ => rfl) rfl
  dia_deco b d P P' a h := by
    classical
    show (d.mv (DecoSet.dia1 P a d.1.1.deco)).1.1.deco.1.f P' = d.1.1.deco.1.f P'
    unfold DecoSet.dia1
    rw [LevLaws.mv_dia]
    funext x
    show ((Pi.mulSingle P a : DiaG X.E ST) P').1 * _ = _
    rw [Pi.mulSingle_eq_of_ne h, Units.val_one, one_mul]
  gam_surj b γ h := by
    obtain ⟨g, hg⟩ := exists_uf γ h
    exact ⟨(g, 1), hg⟩
  T_mem := h1
  T_nsq := h2
  nonconj P hP' Q' hQ' := (hP ⟨P, hP'⟩).st ⟨Q', hQ'⟩

end Split

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem localization_eq_of_sameOff (hPr : Pr.Ok) (u : Pr.Word) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) {n : ℕ}
    {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : SameOff (Pr.vT u) N N') (w : rowSG Pr sel mu) :
    localization₂ w.1.asIdeal N = localization₂ w.1.asIdeal N' := by
  classical
  have h2 : (Pr.T u : 𝓞 X.E) ∉ w.1.asIdeal := (Finset.mem_union.1 w.2).elim (fun h => T_notMem_vGs hPr u ⟨w.1, h⟩) (hQ w.1)
  exact h w.1 fun P hP => ne_of_T_notMem hPr u ⟨P, hP⟩ h2

def splitAt (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)
    (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) (j : ℕ) :
    Split (tdatAt sel mu cst L Tp u j) (Pr.T u) :=
  splitY _ _ _ _ _ _ (moveHyp_of_ok hPr u) (fun P w => ne_of_T_notMem hPr u P (hQ w.1 w.2))
    (fun N N' h => by
      have h1 := localization_eq_of_sameOff sel mu hPr u hQ h
      unfold ysAt
      split_ifs
      · show ybSet sel mu cst N = ybSet sel mu cst N'
        simp only [ybSet, locLat, h1]
      · rfl)
    (fun P hP => (T_unif hX hPr u ⟨P, hP⟩).1) (fun P hP => (T_unif hX hPr u ⟨P, hP⟩).2)

theorem splitAt_off (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)
    (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) (j : ℕ) (b) (p q : PtAt R sel mu cst u j) :
    ((splitAt sel mu cst L Tp hX hPr u hQ j).off b).r p q ↔ SameOffPt sel mu cst u p q := Iff.rfl

theorem frsF_eq (hPr : Pr.Ok) (u : Pr.Word) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) {j : ℕ}
    {p q : PtAt R sel mu cst u j} (h : SameOffPt sel mu cst u p q) : frsF sel mu p.1.1 = frsF sel mu q.1.1 := by
  funext P
  unfold frsF
  split_ifs with hP
  · unfold Deco.liftFr Deco.at
    simp only [localization_eq_of_sameOff sel mu hPr u hQ h.1 P, h.2.1]
  · rw [h.2.2.1]

theorem exists_above_ne (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)
    (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) (j : ℕ) (b) (P : Pr.vT u) (p : PtAt R sel mu cst u j) :
    ∃ q, Above (tdatAt sel mu cst L Tp u j) b P p q ∧ SameOffPt sel mu cst u p q ∧ q ≠ p := by
  classical
  obtain ⟨-, x, hx, hf, -⟩ := p.1.1.deco.upSet_nonempty P (moveHyp_of_ok hPr u P) (T_unif hX hPr u P).1 (T_unif hX hPr u P).2
  refine ⟨_, ⟨x, hx, hf, rfl⟩, (splitAt sel mu cst L Tp hX hPr u hQ j).off_up b p P x hx hf, fun e => ?_⟩
  have h := (tdatAt_tied sel mu cst L Tp hX hPr u hQ j).up_deco b p P x hx hf
  rw [e] at h
  have h3 : p.1.1.deco.1.f P x = if x ∈ localization₂ P.1.asIdeal (upN P.1.asIdeal p.1.1.deco.1.N x)
      then p.1.1.deco.1.f P ((Pr.T u : 𝓞 X.E) • x) else 0 := by
    have := congrFun (congrFun (congrArg Deco.f h) P) x
    simp only [Deco.up, Function.update_self] at this
    exact this
  rw [p.1.1.deco.2.f_smul P _ x (le_locP _ _ hx), Ideal.Quotient.eq_zero_iff_mem.2 (T_unif hX hPr u P).1, zero_mul, ite_self, hf] at h3
  haveI := P.1.isPrime
  exact one_ne_zero h3

end Chain

section Side

variable {D : D7} {u : D.what₂.Word} {B : Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i}

theorem act_of_zeta (R : B.Real i sp M) (ζ : CommGroup.torsion (D.what₂.LL)ˣ) (b) (g : (B.I.S i).G b)
    (h1 : (B.I.S i).gam b g = 1) (h2 : (B.I.S i).chr b g = ζ.1) (d) (y : M.Val) :
    R.zeta ζ • R.pt b d = R.hom b g • R.pt b d ∧ M.act (R.zeta ζ) y = M.act (R.hom b g) y := by
  refine ⟨by rw [← R.pt_smul]; exact (R.inj ζ b d _).2 ⟨g, h1, h2, rfl⟩, Subtype.ext ?_⟩
  rw [R.act_hom, R.act_zeta]
  funext z
  refine Eq.trans ?_ (trFr_apply B.emb D.what₂.embLL _ _ y.1 z).symm
  rw [h1, h2, inv_one]
  exact congrArg (fun t => D.what₂.embLL _ * y.1 t) (frMul_one B.emb D.what₂.embLL z).symm

theorem src_of_kerIs {sp' : Split (B.J.A (i + 1)) B.J.T} {M' : PtModel B.ch (i + 1)} (R : B.Real i sp M)
    (R' : B.Real (i + 1) sp' M') (K : KerPt M M') (k : B.Ker i) (h : Dat.KerIs R R' K k) (b b') (g : (B.I.S i).G b) (d d') (F : B.V i)
    (y : M.Val) (hy : y.1 = B.ev i F) :
    B.ev (i + 1) (k b b' (g • d) d' ((B.I.S i).rho B.emb (B.lam i) b g F)) = B.ev (i + 1) (k b b' d d' F) := by
  rw [← h b b' d d' F y hy, ← h b b' (g • d) d' _ (M.act (R.hom b g) y), R.pt_smul, K.src]
  rw [R.act_hom, hy]
  exact (BuiltChain.evV_rho B.emb D.what₂.embLL (B.I.S i) (B.lam i) b g F).symm

end Side

namespace KerInh

theorem kerEq_unique {D : D7} {u : D.what₂.Word} {B : Dat D u} {i : ℕ} (k k' : B.Ker i) (h : Dat.KerEq k) (h' : Dat.KerEq k') : k = k' := by
  funext b b' d d'
  have e : k b b' ((B.I.S i).rep ((B.I.S i).cl b d)) ((B.I.S (i+1)).rep ((B.I.S (i+1)).cl b' d')) =
      k' b b' ((B.I.S i).rep ((B.I.S i).cl b d)) ((B.I.S (i+1)).rep ((B.I.S (i+1)).cl b' d')) := by
    refine LinearMap.ext fun F => evV_injective B.emb 1 (B.lam (i+1)) D.what₂.embLL (stdFrC _) ?_
    exact (h.kmap ((B.I.S i).cl b d) ((B.I.S (i+1)).cl b' d') F).symm.trans (h'.kmap ((B.I.S i).cl b d) ((B.I.S (i+1)).cl b' d') F)
  rw [← (B.I.S i).mv_smul b d, ← (B.I.S (i+1)).mv_smul b' d', h.equiv, h'.equiv, e]

section K
variable {D : D7} {u : D.what₂.Word} (B : Dat D u)

def id1 {ι R : Type} [CommRing R] {n : ℕ} : ι × Fin n × Fin n → R := fun x => (1 : Matrix (Fin n) (Fin n) R) x.2.1 x.2.2

def I' : ChainIn B.E D.what₂.LL D.what₂.Tau D.R :=
  { B.I with
    rho := fun _ _ => 1
    rho' := fun _ _ => 1
    jet := fun i _ _ => LinearMap.smulRight (MvPolynomial.aeval (R := ℂ) (id1 (R := ℂ))).toLinearMap
      (MvPolynomial.map D.what₂.embLL (extV D.what₂.LL (B.lam (i+1))).1) }

def B' : Dat D u where
  E := B.E
  emb := B.emb
  fok := B.fok
  I := I' B
  J := ⟨B.J.T, B.J.ST, B.J.A, B.J.psi, B.J.duStar, B.J.Dstar, B.J.GamP⟩
  Q := ⟨B.Q.S', B.Q.b0, B.Q.til, B.Q.ext, B.Q.sg, B.Q.tz, B.Q.H⟩
  Z := ⟨B.Z.1, B.Z.2, B.Z.3, B.Z.4, B.Z.5, B.Z.6⟩
  hI := ⟨B.hI.1, fun _ _ _ => norm_one, fun _ _ _ => norm_one, B.hI.4, B.hI.5⟩
  hJ := ⟨B.hJ.1, B.hJ.2, B.hJ.3, B.hJ.4, B.hJ.5, B.hJ.6, B.hJ.7, B.hJ.8, B.hJ.9, B.hJ.10⟩
  hQ := ⟨B.hQ.1, B.hQ.2, B.hQ.3, B.hQ.4, B.hQ.5, B.hQ.6, B.hQ.7, B.hQ.8, B.hQ.9, B.hQ.10, B.hQ.11⟩
  l := ⟨B.l.1, B.l.2, B.l.3, B.l.4⟩
  lf := ⟨B.lf.1, B.lf.2, B.lf.3, B.lf.4, B.lf.5, B.lf.6, B.lf.7, B.lf.8, B.lf.9, B.lf.10, B.lf.11⟩
  hT := ⟨B.hT.1, B.hT.2, B.hT.3⟩

def k0 (i : ℕ) : B.V i →ₗ[D.what₂.LL] B.V (i+1) :=
  LinearMap.smulRight ((MvPolynomial.aeval (R := D.what₂.LL) (id1 (R := D.what₂.LL))).toLinearMap ∘ₗ (Formalism.L2.DIV.VV _ _).subtype) (extV _ _)

def kk (i : ℕ) : B.Ker i := fun b b' d d' =>
  (B.I.S (i+1)).rho B.emb (B.lam (i+1)) b' ((B.I.S (i+1)).mv b' d') ∘ₗ k0 B i ∘ₗ (B.I.S i).rho B.emb (B.lam i) b ((B.I.S i).mv b d)⁻¹

theorem mv_act {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] {n : ℕ} (S : GStep E K n) (h : S.Free) (b) (g : S.G b) (d) :
    S.mv b (g • d) = g * S.mv b d := by
  have e : S.rep (S.cl b (g • d)) = S.rep (S.cl b d) :=
    congrArg (S.rp b) (Quotient.sound (MulAction.mem_orbit d g))
  have h1 := S.mv_smul b (g • d)
  have h2 := S.mv_smul b d
  rw [e] at h1
  have := h b ((g * S.mv b d)⁻¹ * S.mv b (g • d)) (S.rep (S.cl b d)) (by rw [mul_smul, h1, inv_smul_eq_iff, mul_smul, h2])
  exact (inv_mul_eq_one.1 this).symm

theorem mv_rep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] {n : ℕ} (S : GStep E K n) (h : S.Free) (c : S.Cl) :
    S.mv c.1 (S.rep c) = 1 := by
  have h1 := S.mv_smul c.1 (S.rep c)
  have e : S.rep (S.cl c.1 (S.rep c)) = S.rep c := congrArg (S.rp c.1) (S.rp_spec c.1 c.2)
  rw [e] at h1
  exact h _ _ _ h1

theorem polOf_one {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (o : Frames G) (ho : ∀ τ, o.1 τ = 1)
    (s e : ι → ℤ) (h : ∀ τ, 0 ≤ s τ + e τ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    MvPolynomial.aeval (id1 (R := ℂ)) (polOf G 0 o (fun y => (∏ τ, deFr y τ ^ e τ) * fnOf G s 1 P y)) = MvPolynomial.aeval (id1 (R := ℂ)) P := by
  let Q : MvPolynomial (ι × Fin n × Fin n) ℂ := (∏ τ, (Matrix.of fun a b => MvPolynomial.X (τ, a, b) : Matrix (Fin n) (Fin n) (MvPolynomial (ι × Fin n × Fin n) ℂ)).det ^ (s τ + e τ).toNat) * P
  have hd : ∀ (y : ι → Matrix (Fin n) (Fin n) ℂ) τ, MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2)
      (Matrix.of fun a b => MvPolynomial.X (τ, a, b) : Matrix (Fin n) (Fin n) (MvPolynomial (ι × Fin n × Fin n) ℂ)).det = (y τ).det := by
    intro y τ
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp
  have e1 : (fun y : Frames G => (∏ τ, deFr y τ ^ e τ) * fnOf G s 1 P y) = fnOf G 0 (fun τ => (o.1 τ)⁻¹) Q := by
    funext y
    simp only [fnOf, ho, inv_one, Pi.one_apply, one_mul, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, zpow_zero, Finset.prod_const_one, Q,
      map_mul, map_prod, map_pow, hd y.1, deFr]
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_add₀ (y.2 τ).ne_zero, ← zpow_natCast, Int.toNat_of_nonneg (h τ), add_comm]
  rw [e1, polOf_fnOf]
  have := hd (fun _ => 1)
  simp only [Q, map_mul, map_prod, map_pow]
  have h2 : ∀ τ, MvPolynomial.aeval (id1 (R := ℂ)) (Matrix.of fun a b => MvPolynomial.X (τ, a, b) : Matrix (Fin n) (Fin n) (MvPolynomial (ι × Fin n × Fin n) ℂ)).det = 1 :=
    fun τ => (this τ).trans det_one
  simp [h2]

theorem gen {G G' K V V' : Type} [Group G] [Group G'] [Field K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']
    (ρ : G →* Module.End K V) (ρ' : G' →* Module.End K V') (k : V →ₗ[K] V') (g a : G) (g' a' : G') :
    ρ' (g' * a') ∘ₗ k ∘ₗ ρ (g * a)⁻¹ = ρ' g' ∘ₗ (ρ' a' ∘ₗ k ∘ₗ ρ a⁻¹) ∘ₗ ρ g⁻¹ := by
  rw [_root_.mul_inv_rev, map_mul, map_mul]
  rfl

theorem kk_equiv (i : ℕ) (h0 : (B.I.S i).Free) (h1 : (B.I.S (i+1)).Free) (b : (B.I.S i).β) (b' : (B.I.S (i+1)).β) (g : (B.I.S i).G b) (g' : (B.I.S (i+1)).G b') (d : (B.I.S i).D b) (d' : (B.I.S (i+1)).D b') :
    kk B i b b' (g • d) (g' • d') = (B.I.S (i + 1)).rho B.emb (B.lam (i + 1)) b' g' ∘ₗ kk B i b b' d d' ∘ₗ (B.I.S i).rho B.emb (B.lam i) b g⁻¹ := by
  unfold kk
  rw [mv_act _ h0, mv_act _ h1]
  exact gen _ _ _ _ _ _ _

theorem kk_rep (i : ℕ) (h0 : (B.I.S i).Free) (h1 : (B.I.S (i+1)).Free) (c : (B.I.S i).Cl) (c' : (B.I.S (i+1)).Cl) (F : B.V i) :
    kk B i c.1 c'.1 ((B.I.S i).rep c) ((B.I.S (i + 1)).rep c') F = MvPolynomial.aeval (id1 (R := D.what₂.LL)) F.1 • extV D.what₂.LL (B.lam (i+1)) := by
  unfold kk
  rw [mv_rep _ h0, mv_rep _ h1, inv_one, map_one, map_one]
  rfl

theorem kk_kmap (i : ℕ)
    (hs : ∀ τ, 0 ≤ shiftOf (B.lam i) τ + B.ch.C.sSharp i τ) (ht : ∀ τ, shiftOf (B.lam (i+1)) τ = - B.ch.C.sDiv i τ)
    (c : (B.I.S i).Cl) (c' : (B.I.S (i+1)).Cl) (F : B.V i) :
    ((I' B).chain B.emb D.what₂.embLL (B' B).hI (D.hcW u)).Kmap i c c' (B.ev i F) = B.ev (i+1) (MvPolynomial.aeval (id1 (R := D.what₂.LL)) F.1 • extV D.what₂.LL (B.lam (i+1))) := by
    funext (y : Fr B.emb D.what₂.embLL (D.R.N (i+1)))
    have hp := polOf_one (Gr B.emb D.what₂.embLL (D.R.N i)) (fr0 _ _ _) (fun _ => rfl) _ _ hs (MvPolynomial.map D.what₂.embLL F.1)
    show (1 * 1 : ℂ) * ((∏ τ, deFr y τ ^ B.ch.C.sDiv i τ)⁻¹ * fnOf (Gr B.emb D.what₂.embLL (D.R.N (i+1))) 0 1 (MvPolynomial.aeval (id1 (R := ℂ)) (polOf (Gr B.emb D.what₂.embLL (D.R.N i)) 0 (fr0 _ _ _) (fun y => (∏ τ, deFr y τ ^ B.ch.C.sSharp i τ) * fnOf (Gr B.emb D.what₂.embLL (D.R.N i)) (shiftOf (B.lam i)) 1 (MvPolynomial.map D.what₂.embLL F.1) y)) • MvPolynomial.map D.what₂.embLL (extV D.what₂.LL (B.lam (i+1))).1) y) =
      evV B.emb 1 (B.lam (i+1)) D.what₂.embLL (MvPolynomial.aeval (id1 (R := D.what₂.LL)) F.1 • extV D.what₂.LL (B.lam (i+1))) y
    rw [hp, LinearMap.map_smulₛₗ (evV B.emb 1 (B.lam (i+1)) D.what₂.embLL), map_smul, evV_apply]
    have e : MvPolynomial.aeval (id1 (R := ℂ)) (MvPolynomial.map D.what₂.embLL F.1) = D.what₂.embLL (MvPolynomial.aeval (id1 (R := D.what₂.LL)) F.1) := by
      rw [MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
      congr 1
      funext x
      simp [id1, Matrix.one_apply]
    rw [e]
    simp only [fnOf, ht, Pi.smul_apply, smul_eq_mul, Pi.one_apply, one_mul, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, zpow_zero, Finset.prod_const_one, deFr,
      _root_.zpow_neg, Finset.prod_inv_distrib]
    ring

theorem kk_eq (i : ℕ) (h0 : (B.I.S i).Free) (h1 : (B.I.S (i+1)).Free)
    (hs : ∀ τ, 0 ≤ shiftOf (B.lam i) τ + B.ch.C.sSharp i τ) (ht : ∀ τ, shiftOf (B.lam (i+1)) τ = - B.ch.C.sDiv i τ) :
    Dat.KerEq (B := B' B) (kk B i) :=
  ⟨kk_equiv B i h0 h1, fun c c' F => (kk_kmap B i hs ht c c' F).trans (congrArg (B.ev (i+1)) (kk_rep B i h0 h1 c c' F).symm)⟩

theorem eval_extremal {R : Type} [CommRing R] {n : ℕ} (lam : DomWeight n) :
    MvPolynomial.eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0) (extremal R n lam) = 1 := by
  unfold extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  have h : ∀ (k : ℕ) (h1 h2 : k ≤ n),
      (MvPolynomial.eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0)).mapMatrix
        (Matrix.of fun p q : Fin k => (MvPolynomial.X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) R)) = 1 := by
    intro k h1 h2
    ext p q
    simp [Matrix.one_apply, Fin.ext_iff]
  rw [h, Matrix.det_one, one_pow]

theorem ext_one (i : ℕ) : MvPolynomial.aeval (id1 (R := D.what₂.LL)) (extV D.what₂.LL (B.lam i)).1 = 1 := by
  rw [MvPolynomial.aeval_eq_eval]
  show MvPolynomial.eval _ (∏ τ, _) = 1
  rw [map_prod]
  refine Finset.prod_eq_one fun t _ => ?_
  unfold Formalism.GradedWeylDivisibility.blockEmb
  rw [MvPolynomial.eval_rename]
  exact eval_extremal (B.lam i t)

theorem nonzero (i : ℕ) (h0 : (B.I.S i).Free) (h1 : (B.I.S (i+1)).Free) (c : (B.I.S i).Cl) (c' : (B.I.S (i+1)).Cl)
    (hs : ∀ τ, 0 ≤ shiftOf (B.lam i) τ + B.ch.C.sSharp i τ) (ht : ∀ τ, shiftOf (B.lam (i+1)) τ = - B.ch.C.sDiv i τ) :
    ∃ k : (B' B).Ker i, Dat.KerEq k ∧ k ≠ 0 := by
  refine ⟨kk B i, kk_eq B i h0 h1 hs ht, fun e => ?_⟩
  have h := kk_rep B i h0 h1 c c' (extV _ _)
  have e' : kk B i = 0 := e
  rw [ext_one, one_smul, e'] at h
  exact extV_ne_zero _ h.symm
end K

theorem shifts {X : Fields} {R : Ranks} (hc : X.Tau → HCParam R) (i : ℕ) (hi : i < R.m) (τ : X.Tau) :
    0 ≤ shiftOf (GlobalTheory.Mem.Col2.lamT hc i) τ + ⌊(hc τ).e ⟨i, hi⟩ - (R.N (i + 1) : ℚ) / 2⌋ ∧
    shiftOf (GlobalTheory.Mem.Col2.lamT hc (i+1)) τ = - ⌊(hc τ).e ⟨i, hi⟩ - (R.N i : ℚ) / 2⌋ := by
  have h1 := GlobalTheory.GO.ChSrc.trueWt_add_sS_nonneg hc hi τ ⟨R.N i - 1, by have := R.N_pos i; omega⟩
  have h2 := GlobalTheory.GO.ChSrc.trueWt_detShift_succ hc hi τ
  have a : GlobalTheory.GO.ChSrc.sS hc i τ = ⌊(hc τ).e ⟨i, hi⟩ - (R.N (i + 1) : ℚ) / 2⌋ := by
    apply Int.cast_injective (α := ℚ)
    rw [floor_sub_half, GlobalTheory.GO.ChSrc.sS, dif_pos hi]
    exact GlobalTheory.GO.ChSrc.zOf_spec R _ ((hc τ).e_int _) _
  have b : GlobalTheory.GO.ChSrc.sD hc i τ = ⌊(hc τ).e ⟨i, hi⟩ - (R.N i : ℚ) / 2⌋ := by
    apply Int.cast_injective (α := ℚ)
    rw [floor_sub_half, GlobalTheory.GO.ChSrc.sD, dif_pos hi]
    exact GlobalTheory.GO.ChSrc.zOf_spec R _ ((hc τ).e_int _) _
  rw [← a, ← b]
  refine ⟨?_, h2⟩
  unfold shiftOf DomWeight.detShift
  rw [dif_pos (R.N_pos i)]
  exact h1

end KerInh

end GlobalTheory.LvT.Built.Model
