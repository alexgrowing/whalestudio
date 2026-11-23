import Mathlib
import Formalism.LocalToGlobal.Columns.ColForms
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Roots

variable {K : Type} [Field K] [NumberField K]

theorem map_root_smul {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (N : Submodule (𝓞 K) V) (f : Module.End K V) {c : K} {m : ℕ} (hm : 0 < m) (hc : c ^ m = 1) :
    N.map ((c • f).restrictScalars (𝓞 K)) = N.map (f.restrictScalars (𝓞 K)) := by
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hc]⟩
  let c' : 𝓞 K := ⟨c, hint⟩
  have hc' : ∀ x : V, c' • x = c • x := fun x => by
    rw [← algebraMap_smul K c' x]; rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c' • x, N.smul_mem _ hx, ?_⟩
    show f (c' • x) = c • f x
    rw [hc', map_smul]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c' ^ (m - 1) • x, N.smul_mem _ hx, ?_⟩
    show c • f (c' ^ (m - 1) • x) = f x
    have h2 : ∀ (k : ℕ) (x : V), c' ^ k • x = c ^ k • x := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ih => intro x; rw [pow_succ, mul_smul, ih, hc', pow_succ, mul_smul]
    rw [h2, map_smul, smul_smul, ← pow_succ', Nat.sub_add_cancel hm, hc, one_smul]

theorem star_mul_root [StarRing K] (h : ∃ σ₀ : K →+* ℂ, ∀ x : K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    {c : K} {m : ℕ} (hm : 0 < m) (hc : c ^ m = 1) : star c * c = 1 := by
  obtain ⟨σ₀, hσ⟩ := h
  apply σ₀.injective
  rw [map_mul, hσ, map_one, mul_comm, Complex.mul_conj]
  have h1 : ‖σ₀ c‖ = 1 := by
    have : σ₀ c ^ m = 1 := by rw [← map_pow, hc, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one this hm.ne'
  rw [Complex.normSq_eq_norm_sq, h1]
  simp

end Roots

section Form

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

theorem formGSD_smul (a : (formGSD C Λ).G) (d : (formGSD C Λ).D) :
    a • d = ((FormG.incl Λ a : UF X.E n × GLG X.E n SG) • (d : DecoSet X.E n ST SG) : DecoSet X.E n ST SG) := rfl

theorem FormG.incl_injective : Function.Injective (FormG.incl Λ) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 (Subtype.ext h2)

theorem formGSD_rho (a : (formGSD C Λ).G) (x : C.V) :
    (formGSD C Λ).ρ a x = ((Λ.chr a.2 : X.Kˣ) : X.K) • C.rho a.1 x := rfl

theorem mem_formGSD_EqFun (φ : DecoSet X.E n ST SG → C.V) :
    φ ∈ (formGSD C Λ).EqFun ↔ ∀ (γ : UF X.E n) (h : ↥Λ.grp) (d : DecoSet X.E n ST SG),
      φ ((γ, (h : GLG X.E n SG)) • d) = ((Λ.chr h : X.Kˣ) : X.K) • C.rho γ (φ d) :=
  ⟨fun H γ h d => H (γ, h) d, fun H a d => H a.1 a.2 d⟩

theorem LevFam.chr_root (h : ↥Λ.grp) : ∃ m : ℕ, 0 < m ∧ ((Λ.chr h : X.Kˣ) : X.K) ^ m = 1 := by
  have hf : IsOfFinOrder h := isOfFinOrder_of_finite h
  refine ⟨orderOf h, hf.orderOf_pos, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]

theorem formGSD_ok (hX : X.Ok) (hC : C.Eqv) : (formGSD C Λ).Ok where
  fin_orb := by
    obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs
    refine Finite.of_surjective (fun d : s => (formGSD C Λ).cls d.1) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h d =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep d
      refine ⟨⟨d0, hd0⟩, ?_⟩
      refine ((formGSD C Λ).cls_eq_iff d0 d).mpr ⟨((g, 1) : FormG Λ)⁻¹, ?_⟩
      have h1 : d = (((g, 1) : FormG Λ) : (formGSD C Λ).G) • (d0 : (formGSD C Λ).D) := hg
      rw [h1, inv_smul_smul]
  fin_stab := by
    intro d
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (d : DecoSet X.E n ST SG)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (formGSD C Λ).G d =>
        (⟨FormG.incl Λ a.1, a.2⟩ : MulAction.stabilizer (UF X.E n × GLG X.E n SG) (d : DecoSet X.E n ST SG))) ?_
    intro a b hab
    exact Subtype.ext (FormG.incl_injective Λ (congrArg Subtype.val hab))
  nab_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2
    exact (hC.nab_smul (FormG.incl Λ g) d).trans (map_root_smul _ _ hm hc).symm
  del_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2
    exact (hC.del_smul (FormG.incl Λ g) d).trans (map_root_smul _ _ hm hc).symm
  inv := by
    intro g x y
    obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2
    show C.pair (((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 x) (((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star ((Λ.chr g.2 : X.Kˣ) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

theorem formGSD_stab_inj (d : (formGSD C Λ).D) {a b : (formGSD C Λ).G} (ha : a • d = d) (hb : b • d = d)
    (hab : a.1 = b.1) : a = b :=
  FormG.incl_injective Λ (DecoSet.stab_fst_injective (d : DecoSet X.E n ST SG) ha hb hab)

end Form

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem colVal_eqv (hX : X.Ok) (u : Pr.Word) (j : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    (colVal W u j ST SG).Eqv where
  nab_smul := colVal_nab_smul W u j
  del_smul := colVal_del_smul W u j
  inv := roundPk_inv X _ _ hX.emb_star

theorem colOk (hX : X.Ok) (u : Pr.Word) (j : ℕ) : (colGSD W Ch u j).Ok :=
  formGSD_ok _ _ hX (colVal_eqv W hX u j _ _)

theorem colLev_of_lt {j : ℕ} (hj : j < R.m) (w : Pr.vGs) :
    colLev Ch j w = ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j,
      lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j⟩ := if_pos hj

theorem colLev_m (w : Pr.vGs) :
    colLev Ch R.m w = ⟨HXm (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m) R.r R.t R.m,
      lamXm (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N R.m) R.r R.t R.m⟩ := if_neg (lt_irrefl _)

theorem colFree (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    (colGSD W Ch u 0).Free := by
  intro d a ha
  have hpos : 0 < (Pr.vG 0).card := by
    rw [hPr.vG_card 0, Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hw' : w ∈ Pr.vGs := by
    classical
    unfold Primes.vGs
    exact Finset.mem_union_left _ hw
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hmem : (a.2 : GLG X.E (R.N 0) Pr.vGs) ⟨w, hw'⟩ ∈ (colLev Ch 0 ⟨w, hw'⟩).H :=
    (Subgroup.mem_pi _).mp a.2.2 ⟨w, hw'⟩ (Set.mem_univ _)
  rw [colLev_of_lt Ch hm] at hmem
  have h1 : FormG.incl (colLev Ch 0) a = 1 :=
    DecoSet.decoration_stabilizer_trivial_unipotent hX hPr (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs) ha 0 ⟨w, hw'⟩ hw (by rw [hN]; exact hbig)
      (isNilpotent_of_mem_HX_zero hN.le hmem)
  exact FormG.incl_injective _ (h1.trans (map_one _).symm)

theorem finrank_MfV (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    finrank X.K (MfV W Ch u) = Nat.card (colGSD W Ch u 0).Cl * finrank X.K (VV X.K (W.lamTrue u 0)) :=
  (colGSD W Ch u 0).finrank_free (colOk W Ch hX u 0) (colFree W Ch hX hPr hbig u)

theorem ColL_le_ColLnab (u : Pr.Word) (j : ℕ) : ColL W Ch u j ≤ ColLnab W Ch u j := by
  intro φ hφ d
  exact roundPk_del_le X (W.lamTrue u j) (fun d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs => d.1.Lsh) d (hφ d)

theorem map_MfL (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (s : (colGSD W Ch u 0).Sec) :
    (MfL W Ch u).map (((colGSD W Ch u 0).resFree (colOk W Ch hX u 0) s (colFree W Ch hX hPr hbig u) :
      (colGSD W Ch u 0).EqFun →ₗ[X.K] ((colGSD W Ch u 0).Cl → (colGSD W Ch u 0).V)).restrictScalars (𝓞 X.K)) =
      Submodule.pi Set.univ fun c => (colGSD W Ch u 0).Del (s.rep c) :=
  (colGSD W Ch u 0).map_intDel_free (colOk W Ch hX u 0) s (colFree W Ch hX hPr hbig u)

theorem finrank_MfV_pos (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    0 < finrank X.K (MfV W Ch u) := by
  rw [finrank_MfV W Ch hX hPr hbig u]
  have : NeZero (R.N 0) := ⟨(R.N_pos 0).ne'⟩
  have h1 : Finite (colGSD W Ch u 0).Cl := (colOk W Ch hX u 0).fin_orb
  have h2 : Nonempty (colGSD W Ch u 0).Cl :=
    ⟨(colGSD W Ch u 0).cls (DecoSet.base X.E (R.N 0) (Pr.vT u) Pr.vGs)⟩
  exact Nat.mul_pos Nat.card_pos (colVal W u 0 (Pr.vT u) Pr.vGs).finrank_pos

end Cols

end Formalism.L2.Col
