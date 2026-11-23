import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in
theorem exists_mul_add_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 E)) {s : 𝓞 E} (hs : s ∉ w.asIdeal) :
    ∃ t : 𝓞 E, ∃ a ∈ w.asIdeal, t * s + a = 1 :=
  w.isMaximal.exists_inv hs

theorem decoration_admissible_of_localization_eq {d : Deco E n ST SG} (hd : d.Ok) {N' : Submodule (𝓞 E) (Sp E n)}
    (hl : Submodule.IsLattice E N') (hu : IsUnimodular (hStd E n) N')
    (hT : ∀ P : ST, localization₂ P.1.asIdeal d.N = localization₂ P.1.asIdeal N')
    (hG : ∀ w : SG, localization₂ w.1.asIdeal d.N = localization₂ w.1.asIdeal N') :
    Deco.Ok (⟨N', d.f, d.be⟩ : Deco E n ST SG) where
  lat := hl
  uni := hu
  f_add P x hx y hy := hd.f_add P x ((hT P).ge hx) y ((hT P).ge hy)
  f_smul P a x hx := hd.f_smul P a x ((hT P).ge hx)
  f_off P x hx := hd.f_off P x fun h => hx ((hT P).le h)
  f_ne P := by
    obtain ⟨x, hx, hne⟩ := hd.f_ne P
    have hx' := Formalism.L2.Col.le_locP P.1 _ hx
    obtain ⟨s, hs, h⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((hT P).le hx')
    refine ⟨s • x, h, ?_⟩
    change d.f P (s • x) ≠ 0
    rw [hd.f_smul P s x hx']
    haveI := P.1.isPrime
    exact mul_ne_zero (fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)) hne
  be_add w x hx y hy := hd.be_add w x ((hG w).ge hx) y ((hG w).ge hy)
  be_smul w a x hx := hd.be_smul w a x ((hG w).ge hx)
  be_off w x hx := hd.be_off w x fun h => hx ((hG w).le h)
  be_surj w c := by
    obtain ⟨x, hx, hc⟩ := hd.be_surj w c
    have hx' := Formalism.L2.Col.le_locP w.1 _ hx
    obtain ⟨s, hs, h⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((hG w).le hx')
    obtain ⟨t, a, ha, e⟩ := exists_mul_add_eq_one_of_notMem w.1 hs
    refine ⟨(t * s) • x, by rw [mul_smul]; exact N'.smul_mem t h, ?_⟩
    change d.be w ((t * s) • x) = c
    have e1 : Ideal.Quotient.mk w.1.asIdeal (t * s) = 1 := by
      have := congrArg (Ideal.Quotient.mk w.1.asIdeal) e
      rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, add_zero, map_one] at this
    rw [hd.be_smul w _ x hx', e1, one_smul, hc]
  be_ker w x hx h0 := by
    change x ∈ N' at hx
    change d.be w x = 0 at h0
    change x ∈ w.1.asIdeal • N'
    have hx' : x ∈ d.at w.1 := (hG w).ge (Formalism.L2.Col.le_locP w.1 _ hx)
    obtain ⟨s, hs, h⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 hx'
    have h1 : s • x ∈ w.1.asIdeal • d.N := hd.be_ker w _ h (by rw [hd.be_smul w s x hx', h0, smul_zero])
    have h2 : w.1.asIdeal • d.N ≤ localization₂ w.1.asIdeal (w.1.asIdeal • N') := by
      refine Submodule.smul_le.2 fun a ha y hy => ?_
      obtain ⟨u, hu, hy'⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((hG w).le (Formalism.L2.Col.le_locP w.1 _ hy))
      refine (Formalism.L2.Col.mem_locP _ _ _).2 ⟨u, hu, ?_⟩
      rw [smul_comm]
      exact Submodule.smul_mem_smul ha hy'
    obtain ⟨u, hu, h3⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 (h2 h1)
    have hus : u * s ∉ w.1.asIdeal := fun hm => (w.1.isPrime.mem_or_mem hm).elim hu hs
    obtain ⟨t, a, ha, e⟩ := exists_mul_add_eq_one_of_notMem w.1 hus
    have e2 : x = t • (u • s • x) + a • x := by
      rw [← mul_smul, ← mul_smul, ← add_smul, mul_assoc, e, one_smul]
    rw [e2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ t h3) (Submodule.smul_mem_smul ha hx)

omit [StarRing E] in

theorem exists_coprime_mem (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ Q ∈ S, ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal) : ∃ a : ℕ, a.Coprime p ∧ ∀ Q ∈ S, ((a : ℕ) : 𝓞 E) ∈ Q.asIdeal := by
  classical
  have h1 : ∀ Q : S, ∃ a : ℕ, a.Coprime p ∧ ((a : ℕ) : 𝓞 E) ∈ Q.1.asIdeal := by
    intro Q
    haveI := Q.1.isMaximal
    haveI : Finite (𝓞 E ⧸ Q.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.1.ne_bot
    letI := Ideal.Quotient.field Q.1.asIdeal
    have hp : (ringChar (𝓞 E ⧸ Q.1.asIdeal)).Prime := CharP.prime_ringChar _
    refine ⟨_, (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hS Q.1 Q.2 ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 h
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 dvd_rfl
  choose a ha ha' using h1
  refine ⟨∏ Q, a Q, Nat.Coprime.prod_left fun Q _ => ha Q, fun Q hQ => ?_⟩
  exact Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem a (Finset.mem_univ ⟨Q, hQ⟩))) (ha' ⟨Q, hQ⟩)

end Deco

section Coef

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K)

theorem natCast_notMem_of_coprime {a p : ℕ} (h : a.Coprime p) (w : HeightOneSpectrum (𝓞 K))
    (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro ha
  obtain ⟨x, y, e⟩ := (Nat.Coprime.cast (R := 𝓞 K) h)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ ha) (w.asIdeal.mul_mem_left _ hw)))

omit [Fintype ι] in
theorem nsmul_mem_tauLat (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    {y : Fin n → K} (hy : y ∈ tauLat emb τ L) : a • y ∈ tauLat emb τ L' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a • x, h x hx, ?_⟩
    funext i
    simp
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

omit [Fintype ι] in
theorem localization_dualFr_tauLat_le (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (dualFr (tauLat emb τ L')) ≤ localization₂ w.asIdeal (dualFr (tauLat emb τ L)) := by
  refine GlobalTheory.TransLoc.localization_le_of_smul_mem w ha fun φ hφ x hx => ?_
  have := hφ _ (nsmul_mem_tauLat emb τ h hx)
  rw [dotProduct_smul] at this
  rw [smul_dotProduct, Nat.cast_smul_eq_nsmul]
  exact this

theorem localization_nabK_delK_congr (lam : ι → DomWeight n) {M M' : ι → Submodule (𝓞 K) (Fin n → K)}
    (hM : ∀ τ, Submodule.IsLattice K (M τ)) (hM' : ∀ τ, Submodule.IsLattice K (M' τ)) (w : HeightOneSpectrum (𝓞 K))
    (h : ∀ τ, localization₂ w.asIdeal (M τ) = localization₂ w.asIdeal (M' τ)) :
    localization₂ w.asIdeal (nabK lam M) = localization₂ w.asIdeal (nabK lam M') ∧
      localization₂ w.asIdeal (delK lam M) = localization₂ w.asIdeal (delK lam M') := by
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
  have hB' : ∀ τ, IsBasisAt w (M' τ) (B τ) := fun τ => (h τ).symm.trans (hB τ)
  have h1 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB
  have h2 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M' hM' w B hB'
  have key : ∀ (T : Submodule (𝓞 K) (Pol K ι n)) (x : VV K lam),
      x ∈ localization₂ w.asIdeal (T.comap ((VV K lam).subtype.restrictScalars (𝓞 K))) ↔ x.1 ∈ localization₂ w.asIdeal T := by
    intro T x
    exact Iff.rfl
  constructor
  · ext x
    unfold nabK
    rw [key, key, h1.1, h2.1]
  · ext x
    unfold delK
    rw [key, key, h1.2, h2.2]

theorem localization_nabAtr_delAtr_congr (lam : ι → DomWeight n) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (h' : ∀ x ∈ L', a • x ∈ L) (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr emb lam L) = localization₂ w.asIdeal (nabAtr emb lam L') ∧
      localization₂ w.asIdeal (delAtr emb lam L) = localization₂ w.asIdeal (delAtr emb lam L') :=
  localization_nabK_delK_congr lam
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L hL))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L' hL')) w
    fun τ => le_antisymm (localization_dualFr_tauLat_le emb τ h' w ha) (localization_dualFr_tauLat_le emb τ h w ha)

end Coef

variable {p : ℕ} {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem use₃ (lam : X.Tau → DomWeight n) (hT : ∀ Q ∈ ST, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal)
    (d : DecoSet X.E n ST SG) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (nabAtr X.emb lam d.1.N) ∧
      localization₂ w.asIdeal (delAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (delAtr X.emb lam d.1.N) := by
  obtain ⟨a, hap, ha⟩ := exists_coprime_mem p ST hT
  refine localization_nabAtr_delAtr_congr X.emb lam d.2.Lsh_lattice d.2.lat (a := a) (fun x hx => ?_)
    (fun x hx => Submodule.smul_of_tower_mem _ a (d.2.N_le_Lsh hx)) w (natCast_notMem_of_coprime hap w hw)
  rw [← Nat.cast_smul_eq_nsmul (𝓞 X.E)]
  exact d.2.smul_Lsh_mem_N (fun P => by rw [map_natCast]; exact ha P.1 P.2) hx

theorem levFam_chr_root (Λ : LevFam X.E X.K n SG) (g : Λ.grp) : ∃ k : ℕ, 0 < k ∧ Λ.chr g ^ k = 1 := by
  haveI : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w => Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  haveI : Finite (GLG X.E n SG) := inferInstance
  refine ⟨orderOf g, orderOf_pos g, ?_⟩
  rw [← map_pow, pow_orderOf_eq_one, map_one]

def psysForm (lam : X.Tau → DomWeight n) (Λ : LevFam X.E X.K n SG)
    (hT : ∀ Q ∈ ST, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal) (hG : ∀ Q ∈ SG, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal) :
    PSys X n p lam (formGSD (roundPk X lam fun d : DecoSet X.E n ST SG => d.1.Lsh) Λ) where
  u := MonoidHom.fst _ _
  chr := Λ.chr.comp (MonoidHom.snd _ _)
  eV := LinearEquiv.refl _ _
  N d := d.1.N
  Aw d d' := SameOff p d.1.N d'.1.N ∧ d.1.f = d'.1.f ∧ d.1.be = d'.1.be
  aw_equiv :=
    ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl⟩, fun h => ⟨fun Q hQ => (h.1 Q hQ).symm, h.2.1.symm, h.2.2.symm⟩,
      fun h h' => ⟨fun Q hQ => (h.1 Q hQ).trans (h'.1 Q hQ), h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩⟩
  aw_smul g d d' h := by
    refine ⟨fun Q hQ => ?_, ?_, ?_⟩
    · ext x
      change x ∈ localization₂ Q.asIdeal (gmap g.1.1 d.1.N) ↔ x ∈ localization₂ Q.asIdeal (gmap g.1.1 d'.1.N)
      rw [mem_localization_gmap, mem_localization_gmap, h.1 Q hQ]
    · change (d.1.act g.1.1 g.2.1).f = (d'.1.act g.1.1 g.2.1).f
      simp only [Deco.act, h.2.1]
    · change (d.1.act g.1.1 g.2.1).be = (d'.1.act g.1.1 g.2.1).be
      simp only [Deco.act, h.2.2]
  aw_off _ _ h := h.1
  aw_ex d N' hl hu hs := by
    refine ⟨⟨⟨N', d.1.f, d.1.be⟩, decoration_admissible_of_localization_eq d.2 hl hu (fun P => hs _ (hT _ P.2)) fun w => hs _ (hG _ w.2)⟩,
      ⟨⟨hs, rfl, rfl⟩, rfl⟩, ?_⟩
    rintro d' ⟨⟨-, hf, hb⟩, hN⟩
    exact Subtype.ext (Deco.ext hN hf.symm hb.symm)
  lat d := d.2.lat
  uni d := d.2.uni
  N_smul _ _ := rfl
  chr_root g := levFam_chr_root Λ g.2
  rho _ _ := rfl
  del d w hw x := by
    rw [← (use₃ lam hT d w hw).2]
    rfl
  nab d w hw x := by
    rw [← (use₃ lam hT d w hw).1]
    rfl

def psysCol {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (u : Pr.Word) (j : ℕ)
    (hT : ∀ Q ∈ Pr.vT u, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal) (hG : ∀ Q ∈ Pr.vGs, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal) :
    PSys X (R.N j) p (W.lamTrue u j) (colGSD W Ch u j) :=
  psysForm (W.lamTrue u j) (colLev Ch j) hT hG

end GlobalTheory.GO
