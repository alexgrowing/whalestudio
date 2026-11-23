import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen

noncomputable section

namespace GlobalTheory.Mem.Col2.BwLat

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.LvT.Built.ValLat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem natCast_notMem {T : ℕ} (hT : T.Prime) (Q : HeightOneSpectrum (𝓞 E)) (hQ : (T : 𝓞 E) ∈ Q.asIdeal) {s : ℕ}
    (hs : ¬ T ∣ s) : (s : 𝓞 E) ∉ Q.asIdeal := by
  intro h
  have hc : IsCoprime (T : 𝓞 E) (s : 𝓞 E) := ((Nat.Prime.coprime_iff_not_dvd hT).2 hs).cast
  obtain ⟨a, b, e⟩ := hc
  exact one_notMem Q (e ▸ add_mem (Q.asIdeal.mul_mem_left a hQ) (Q.asIdeal.mul_mem_left b h))

theorem isBasisAt_of_isLocBasis {T : ℕ} (hT : T.Prime) (Q : HeightOneSpectrum (𝓞 E)) (hQ : (T : 𝓞 E) ∈ Q.asIdeal)
    {L : Submodule (𝓞 E) (Fin n → E)} {B : GL (Fin n) E} (h : IsLocBasis T (L : Set (Fin n → E)) B) : IsBasisAt Q L B := by
  classical
  unfold IsBasisAt
  ext x
  rw [mem_localized_columnLattice_iff]
  constructor
  · intro hx a
    obtain ⟨t, ht, hx⟩ := (mem_locP Q _ _).1 hx
    obtain ⟨s, hs, h2⟩ := (h (t • x)).1 ⟨1, hT.not_dvd_one, by simpa using hx⟩
    refine (mem_locP Q _ _).2 ⟨(s : 𝓞 E) * t, fun hm => (Q.isPrime.mem_or_mem hm).elim (natCast_notMem hT Q hQ hs) ht, ?_⟩
    obtain ⟨r, hr⟩ := h2 a
    refine Submodule.mem_one.2 ⟨r, hr.trans ?_⟩
    rw [← algebraMap_smul E t x, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul, map_natCast, mul_assoc]
  · intro hx
    choose t ht hx using fun a => (mem_locP Q _ _).1 (hx a)
    have ht' : ∏ a, t a ∉ Q.asIdeal := fun hm => by
      obtain ⟨a, -, ha⟩ := (Ideal.IsPrime.prod_mem_iff (hp := Q.isPrime)).1 hm
      exact ht a ha
    obtain ⟨s, hs, h2⟩ := (h ((∏ a, t a) • x)).2 ⟨1, hT.not_dvd_one, fun a => by
      have h3 := Submodule.smul_mem _ (∏ b ∈ Finset.univ.erase a, t b) (hx a)
      rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ a)] at h3
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 h3
      refine ⟨r, hr.trans ?_⟩
      rw [← algebraMap_smul E _ x, Matrix.mulVec_smul, Algebra.smul_def, Nat.cast_one, one_mul]
      rfl⟩
    refine (mem_locP Q _ _).2 ⟨(s : 𝓞 E) * ∏ a, t a,
      fun hm => (Q.isPrime.mem_or_mem hm).elim (natCast_notMem hT Q hQ hs) ht', ?_⟩
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    rwa [Nat.cast_smul_eq_nsmul] at h2

variable {K ι : Type} [Field K] [NumberField K] [Fintype ι]

theorem mem_localization_delAtr_fn (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K))
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : Submodule.IsLattice E L) (B : ι → GL (Fin n) E)
    (hB : ∀ τ, IsBasisAt (bcBelow (emb τ) w) L (B τ)) (F : Formalism.L2.DIV.VV K lam) :
    F ∈ localization₂ w.asIdeal (delAtr emb lam L) ↔ ∃ z ∈ localization₂ w.asIdeal (delStd K lam),
      evV emb 1 lam σ F = fnOf _ (shiftOf lam)
        (fun τ => atInf (embAt σ emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ) (MvPolynomial.map σ z) := by
  rw [mem_localization_delAtr emb lam w hL (fun τ => inside₂ K n (Formalism.UG.bc (emb τ) (B τ))) (fun τ =>
    pb_isBasisAt_dualFr w _ (tauLatLattice E K ι n emb τ L hL).fg _ (bc_isBasisAt (emb τ) w (hB τ)))]
  refine exists_congr fun z => and_congr_right fun _ => ?_
  have h := evFr_actP (gramC (1 : Matrix (Fin n) (Fin n) E) (embAt σ emb)) σ lam
    (fun τ => inside₂ K n (Formalism.UG.bc (emb τ) (B τ))) z
  have e : (fun τ => (((inside₂ K n (Formalism.UG.bc (emb τ) (B τ)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ) =
      fun τ => atInf (embAt σ emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ := by
    funext τ
    ext a b
    simp only [inside₂, atInf, embAt, Formalism.UG.bc, transpose_apply, map_apply, RingHom.comp_apply, ← map_inv]
    rfl
  rw [e] at h
  rw [← h]
  exact ⟨fun h' => by rw [← h']; rfl, fun h' => evFr_injective _ _ σ (stdFrC _) h'⟩

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem localization_LshKer_eq_localization_sup {d : Deco E n ST SG} (hd : d.Ok) {a : 𝓞 E} (ha : SepElt ST a) (P : ST) :
    localization₂ P.1.asIdeal (d.LshKer P) = localization₂ P.1.asIdeal (d.L ⊔ P.1.asIdeal • d.Lsh) := by
  apply le_antisymm
  · refine localization_le_of_le_localization _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := (hd.mem_LshKer ha P x).1 hx
    exact localization_mono _ le_sup_left ((hd.mem_locP_L P x).2 ⟨hd.Lsh_le_at ha P h1, h2⟩)
  · refine localization_mono _ (sup_le (fun x hx => (hd.mem_LshKer ha P x).2 ⟨hd.L_le_Lsh hx, ((hd.mem_L x).1 hx).2 P⟩) ?_)
    refine Submodule.smul_le.2 fun p hp x hx => (hd.mem_LshKer ha P _).2 ⟨Submodule.smul_mem _ p hx, ?_⟩
    rw [hd.f_smul P p x (hd.Lsh_le_at ha P hx), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]

theorem lattice_sup_smul {d : Deco E n ST SG} (hd : d.Ok) (I : Ideal (𝓞 E)) :
    Submodule.IsLattice E (d.L ⊔ I • d.Lsh : Submodule (𝓞 E) (Sp E n)) :=
  lattice_between hd.L_lattice hd.Lsh_lattice le_sup_left (sup_le hd.L_le_Lsh Submodule.smul_le_right)

open Classical in

theorem mem_localization_ker (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K))
    {T : ℕ} (hT : T.Prime) (hST : ∀ P : ST, (T : 𝓞 E) ∈ P.1.asIdeal) (e : ST ≃ ι) (he : ∀ P, bcBelow (emb (e P)) w = P.1)
    {d : Deco E n ST SG} (hd : d.Ok) {a : 𝓞 E} (ha : SepElt ST a) (P : ST) {B B' : GL (Fin n) E}
    (hB : IsLocBasis T (d.Lsh : Set (Fin n → E)) B)
    (hB' : IsLocBasis T ((d.L ⊔ P.1.asIdeal • d.Lsh : Submodule (𝓞 E) (Sp E n)) : Set (Fin n → E)) B')
    (F : Formalism.L2.DIV.VV K lam) :
    F ∈ localization₂ w.asIdeal (delAtr emb lam (d.LshKer P)) ↔ ∃ z ∈ localization₂ w.asIdeal (delStd K lam),
      evV emb 1 lam σ F = fnOf _ (shiftOf lam)
        (fun τ => if τ = e P then atInf (embAt σ emb) ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ
          else atInf (embAt σ emb) ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ) (MvPolynomial.map σ z) := by
  rw [mem_localization_delAtr_fn emb σ lam w (hd.LshKer_lattice ha P) (fun τ => if τ = e P then B' else B)]
  · have e1 : (fun τ => atInf (embAt σ emb) (((if τ = e P then B' else B)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ) =
        fun τ => if τ = e P then atInf (embAt σ emb) ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ
          else atInf (embAt σ emb) ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ := by
      funext τ
      split_ifs <;> rfl
    rw [e1]
  · intro τ
    obtain ⟨Q, rfl⟩ := e.surjective τ
    rw [he]
    by_cases hQ : Q = P
    · subst hQ
      rw [if_pos rfl]
      exact (localization_LshKer_eq_localization_sup hd ha Q).trans (isBasisAt_of_isLocBasis hT Q.1 (hST Q) hB')
    · rw [if_neg fun h => hQ (e.injective h)]
      exact (hd.locP_LshKer_ne ha hQ).trans (isBasisAt_of_isLocBasis hT Q.1 (hST Q) hB)

theorem dualL_std (s : E →+* E) (hs : ∀ x, s x = star x) (L : Submodule (𝓞 E) (Sp E n)) :
    dualL s (1 : Matrix (Fin n) (Fin n) E) L = dual (hStd E n) L := by
  have e : dualSet s (1 : Matrix (Fin n) (Fin n) E) L = (dual (hStd E n) L : Set (Sp E n)) := by
    ext y
    rw [SetLike.mem_coe, mem_dual]
    refine forall₂_congr fun x _ => ?_
    have : Formalism.UG.hform s (1 : Matrix (Fin n) (Fin n) E) x y = hStd E n x y := by
      simp [Formalism.UG.hform, hStd_apply, Matrix.one_apply, hs]
    rw [this, Submodule.mem_one]
    rfl
  rw [dualL, e, Submodule.span_eq]

theorem mem_localization_latticeOf [StarRing K] (S : GStep E K n) [Finite S.Cl] (emb : ι → E →+* K) (lam : ι → DomWeight n)
    (h : (S.fam emb lam).Ok) (M : S.Cl → Submodule (𝓞 K) (Formalism.L2.DIV.VV K lam)) (w : HeightOneSpectrum (𝓞 K))
    (x : S.FormsK emb lam h) :
    (∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ S.latOf emb lam h M) ↔ ∀ c, x.1 c ∈ localization₂ w.asIdeal (M c) := by
  classical
  constructor
  · rintro ⟨s, hs, hx⟩ c
    exact (mem_locP w _ _).2 ⟨s, hs, hx c⟩
  · intro hx
    haveI := Fintype.ofFinite S.Cl
    choose t ht hx using fun c => (mem_locP w _ _).1 (hx c)
    refine ⟨∏ c, t c, fun hm => ?_, fun c => ?_⟩
    · obtain ⟨a, -, ha⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hm
      exact ht a ha
    · have h3 := Submodule.smul_mem _ (∏ b ∈ Finset.univ.erase c, t b) (hx c)
      rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ c)] at h3
      exact h3

theorem fnOf_eq {G G' : ι → Matrix (Fin n) (Fin n) ℂ} {s s' : ι → ℤ} {M M' : ι → Matrix (Fin n) (Fin n) ℂ} (hs : s = s')
    (hM : ∀ τ, M τ = M' τ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) (y' : Frames G') (h : y.1 = y'.1) :
    fnOf G s M P y = fnOf G' s' M' P y' := by
  obtain rfl : M = M' := funext hM
  subst hs
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, h]

theorem ite_atInf {p : Prop} (d d' : Decidable p) {e e' : ι → E →+* ℂ} (h : e = e') (A B : Matrix (Fin n) (Fin n) E) (τ : ι) :
    @ite _ p d (atInf e A τ) (atInf e B τ) = @ite _ p d' (atInf e' A τ) (atInf e' B τ) := by
  subst h
  congr

end Gen

end GlobalTheory.Mem.Col2.BwLat

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Mem.Col2.BwLat GlobalTheory.LvT.Built.ValLat Formalism.HermitianLatticesTheory

set_option maxHeartbeats 1000000 in

theorem bw_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY → BwTieG (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) eY (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) := by
  intro B X I hI hP l Z u a i hi eY hY w hw hs v x
  revert hw hs
  change HeightOneSpectrum (𝓞 B.fields.K) at w
  intro hw hs
  obtain ⟨hG, -, hc⟩ := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hL := (hc u a).1
  have hX := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  have hs' : seenC (B.primes X) u w := @of_decide_eq_true _ (Classical.propDecidable _) hs
  have hT : (B.T u).Prime := l.pr.T_prime u
  haveI : Fact (B.T u).Prime := ⟨hT⟩
  have hd : ∀ c, LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = ((I.stp u a i).rep c).1.1.deco.1.Lsh := by
    intro c
    have h1 := dualL_std (E := B.host.E) (sigD (I.rec7 l Z)).toRingHom (fun x => rfl) ((I.stp u a i).rep c).1.1.deco.1.L
    exact (congrArg₂ (dualL _) hG (hL c)).trans h1
  have hk : ∀ c, LkG (I.rec7 l Z) i hi (PvG (D := I.rec7 l Z) (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) =
      ((I.stp u a i).rep c).1.1.deco.1.L ⊔ v.1.asIdeal • ((I.stp u a i).rep c).1.1.deco.1.Lsh := by
    intro c
    have e : PvG (D := I.rec7 l Z) (I.resT l u a) v = v.1.asIdeal := Ideal.mk_ker (I := (v.1.asIdeal : Ideal (𝓞 B.host.E)))
    exact congrArg₂ (· ⊔ ·) (hL c) (congrArg₂ (· • ·) e (hd c))
  have hlam : lamTG (D := I.rec7 l Z) (I.fm l u a) i = GlobalTheory.Mem.Col2.lamT (B.hcW u) i := by
    funext τ
    show Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) i) ((i * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) i) (-((i : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : (B.R.t + 1) / 2 = k + 1 := by omega
    have e2 : i * (B.R.t + 1) / 2 = i * (k + 1) := by
      rw [show B.R.t + 1 = (k + 1) * 2 by omega, ← mul_assoc, Nat.mul_div_cancel _ two_pos]
    unfold Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
    congr 1
    funext j
    rw [e1, e2, Nat.cast_mul, sub_eq_add_neg]
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hint : ∀ P, P ∈ IntSpan (I.rec7 l Z) w ((I.fm l u a).lam i) ↔
      ∃ z₀ ∈ localization₂ w.asIdeal (delStd B.LL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i)), P = MvPolynomial.map B.embLL z₀ := by
    intro P
    have h := mem_closure_iff (I.rec7 l Z).what₂.embLL ((I.rec7 l Z).plEq w) (intW (I.rec7 l Z).what₂.places w)
      ((I.rec7 l Z).val_nonneg_iff w) (lamTG (D := I.rec7 l Z) (I.fm l u a) i) P
    simp only [lamTG, delSq_shW] at h
    rw [← hlam]
    exact h
  have hfin : Finite (I.stp u a i).Cl := by
    haveI := ((l.ch u a).step i).fin_orb
    exact Finite.instSigma
  have h1 : x ∈ (I.fm l u a).Bw i w v ↔ ∀ c, x.1 c ∈ localization₂ w.asIdeal
      (delAtr B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) (((I.stp u a i).rep c).1.1.deco.1.LshKer v)) :=
    ((I.rec7 l Z).mem_locW_iff w _ x).trans
      (mem_localization_latticeOf (I.stp u a i) B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) ((l.fmL u a).fam i) _ w x)
  refine h1.trans (forall_congr' fun c => ?_)
  have key : ∀ Bm Bm' : GL (Fin (B.R.N i)) B.host.E,
      IsLocBasis (B.T u) (((I.stp u a i).rep c).1.1.deco.1.Lsh : Set _) Bm →
      IsLocBasis (B.T u) ((((I.stp u a i).rep c).1.1.deco.1.L ⊔ v.1.asIdeal • ((I.stp u a i).rep c).1.1.deco.1.Lsh :
        Submodule (𝓞 B.host.E) _) : Set _) Bm' →
      (x.1 c ∈ localization₂ w.asIdeal
        (delAtr B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) (((I.stp u a i).rep c).1.1.deco.1.LshKer v)) ↔
      ∃ P ∈ IntSpan (I.rec7 l Z) w ((I.fm l u a).lam i), ∀ z, (I.fm l u a).emb i x c z =
        fnOf _ (shiftOf (lamTG (D := I.rec7 l Z) (I.fm l u a) i))
          (fun τ => @ite _ (τ = (I.fm l u a).tauOf w v) (Classical.propDecidable _)
            (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Bm'⁻¹ : GL (Fin (B.R.N i)) B.host.E).1 τ)
            (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Bm⁻¹ : GL (Fin (B.R.N i)) B.host.E).1 τ)) P (eY z)) := by
    intro Bm Bm' hB hB'
    refine (mem_localization_ker B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) w hT (T_mem_vT l.pr u) (tauAt l.pr u w)
      (fun P => seesP_tauAt l.pr u hX hs' P) ((I.stp u a i).rep c).1.1.deco.2 (sepElt_of_ok l.pr u) v hB hB' (x.1 c)).trans ?_
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨_, (hint _).2 ⟨z, hz, rfl⟩, fun y => (congrFun e y).trans ?_⟩
      exact fnOf_eq (congrArg shiftOf hlam.symm) (fun τ => ite_atInf _ _ hemb.symm _ _ τ) _ _ _ (hY y).symm
    · rintro ⟨P, hP, e⟩
      obtain ⟨z, hz, rfl⟩ := (hint P).1 hP
      refine ⟨z, hz, funext fun y => (e y).trans ?_⟩
      exact fnOf_eq (congrArg shiftOf hlam) (fun τ => ite_atInf _ _ hemb _ _ τ) _ _ _ (hY y)
  constructor
  · intro h Bm Bm' hB hB'
    rw [hd c] at hB
    rw [hk c] at hB'
    exact (key Bm Bm' hB hB').1 h
  · intro h
    have l1 := ((I.stp u a i).rep c).1.1.deco.2.Lsh_lattice
    have l2 := lattice_sup_smul ((I.stp u a i).rep c).1.1.deco.2 v.1.asIdeal
    obtain ⟨Bm, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (B.T u) B.host.E _ l1.fg l1.span_eq_top
    obtain ⟨Bm', hB'⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (B.T u) B.host.E _ l2.fg l2.span_eq_top
    exact (key Bm Bm' hB hB').2 (h Bm Bm' (by rw [hd c]; exact hB) (by rw [hk c]; exact hB'))

end GlobalTheory.Mem.Col2.TC

end
