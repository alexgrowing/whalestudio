import Mathlib
import Formalism.LocalToGlobal.Columns.BrzColLatOneLattice

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality Formalism.HermitianLatticesTheory

section Orth

variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)

def brzo_perp (x : A.V) : Submodule (𝓞 K) A.V where
  carrier := {y | ∀ v, majAt A.b A.X v x y = 0}
  add_mem' := by
    intro a b ha hb v
    have h : majAt A.b A.X v x (a + b) = majAt A.b A.X v x a + majAt A.b A.X v x b := ((isSesq_maj A.b A.X) v).2.1 x a b
    rw [h, ha v, hb v, add_zero]
  zero_mem' := by
    intro v
    have h : majAt A.b A.X v x ((0 : K) • (0 : A.V)) = v.embedding (0 : K) * majAt A.b A.X v x 0 :=
      ((isSesq_maj A.b A.X) v).2.2.2 (0 : K) x 0
    simpa using h
  smul_mem' := by
    intro c y hy v
    have h : majAt A.b A.X v x (algebraMap (𝓞 K) K c • y) = v.embedding (algebraMap (𝓞 K) K c) * majAt A.b A.X v x y :=
      ((isSesq_maj A.b A.X) v).2.2.2 (algebraMap (𝓞 K) K c) x y
    rw [algebraMap_smul] at h
    rw [h, hy v, mul_zero]

variable {A} {γ : Type} [DecidableEq γ] (N : γ → Submodule (𝓞 K) A.V)

theorem brzo_orth_sup (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0)
    (a : γ) (s : Finset γ) (ha : a ∉ s) : ∀ x ∈ N a, ∀ y ∈ ⨆ c ∈ s, N c,
    inner ℝ (realize A.b A.X x) (realize A.b A.X y) = 0 := by
  intro x hx y hy
  have hle : (⨆ c ∈ s, N c) ≤ brzo_perp A x :=
    iSup₂_le fun c hc z hz v => horth a c (fun h => ha (h ▸ hc)) x hx z hz v
  rw [Formalism.HN.HeightGram.inner_realize]
  exact Finset.sum_eq_zero fun v _ => by rw [hle hy v]; rfl

theorem hlat_orth_fin (hA : FrameOK A) (hfg : ∀ c, (N c).FG) (hne : ∀ c, N c ≠ ⊥)
    (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0) (s : Finset γ) :
    Formalism.HN.deg (realize A.b A.X) (⨆ c ∈ s, N c) = ∑ c ∈ s, Formalism.HN.deg (realize A.b A.X) (N c) ∧
    (s.Nonempty → (⨆ c ∈ s, N c) ≠ ⊥ ∧ ∀ θ : ℝ, (∀ c ∈ s, Formalism.HN.muMax (realize A.b A.X) (N c) ≤ θ) →
      Formalism.HN.muMax (realize A.b A.X) (⨆ c ∈ s, N c) ≤ θ) := by
  have hlat : ∀ L : Submodule (𝓞 K) A.V, L.FG → Formalism.HN.IsLat (realize A.b A.X) L :=
    fun L hL => (Formalism.HN.plLat K A.V A.ι A.b A.X hA L hL).1
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, fun h => absurd h Finset.not_nonempty_empty⟩
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Finset.sum_empty]
    exact (Formalism.HN.satBasic (𝓞 K) A.V _ (realize A.b A.X) ⊥ (hlat ⊥ Submodule.fg_bot)).2.2.2.2.1
  | insert a s ha ih =>
    have hfs : (⨆ c ∈ s, N c).FG := Submodule.fg_biSup s N fun c _ => hfg c
    obtain ⟨-, h2, h3⟩ := (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) A.V _ (realize A.b A.X)).2 (N a) (⨆ c ∈ s, N c) (hlat _ (hfg a)) (hlat _ hfs)
      (brzo_orth_sup N horth a s ha)
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    refine ⟨by rw [h2, ih.1], fun _ => ⟨fun h => hne a (eq_bot_iff.2 (h ▸ le_sup_left)), fun θ hθ => ?_⟩⟩
    by_cases hs : s.Nonempty
    · obtain ⟨i1, i2⟩ := ih.2 hs
      rw [(h3 (hne a) i1).1]
      exact max_le (hθ a (Finset.mem_insert_self _ _)) (i2 θ fun c hc => hθ c (Finset.mem_insert_of_mem hc))
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, sup_bot_eq]
      exact hθ a (Finset.mem_insert_self _ _)

theorem hlat_orth_sum [Fintype γ] [Nonempty γ] (hA : FrameOK A) (hfg : ∀ c, (N c).FG) (hne : ∀ c, N c ≠ ⊥)
    (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0)
    (r : ℕ) (hr : 0 < r) (hrk : ∀ c, Formalism.HN.rkK (N c) = r) (hrkT : Formalism.HN.rkK (⨆ c, N c) = Fintype.card γ * r) :
    (withL A (⨆ c, N c)).mu = mean (fun c => (withL A (N c)).mu) ∧
    ∃ c, (withL A (⨆ c, N c)).muMax ≤ (withL A (N c)).muMax := by
  have hsup : (⨆ c, N c) = ⨆ c ∈ (Finset.univ : Finset γ), N c := by simp
  obtain ⟨h1, h2⟩ := hlat_orth_fin N hA hfg hne horth Finset.univ
  rw [← hsup] at h1 h2
  have hfT : (⨆ c, N c).FG := by rw [hsup]; exact Submodule.fg_biSup _ N fun c _ => hfg c
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcard : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hsl : ∀ c, Formalism.HN.slope (realize A.b A.X) (N c) =
      Formalism.HN.deg (realize A.b A.X) (N c) / ((Module.finrank ℚ K : ℝ) * r) := by
    intro c
    have := (Formalism.HN.plLat K A.V A.ι A.b A.X hA (N c) (hfg c)).2.1
    show Formalism.HN.deg (realize A.b A.X) (N c) / ((Formalism.HN.rk (realize A.b A.X) (N c) : ℕ) : ℝ) = _
    rw [this, hrk c]
    push_cast
    rfl
  have hslT : Formalism.HN.slope (realize A.b A.X) (⨆ c, N c) =
      (∑ c, Formalism.HN.deg (realize A.b A.X) (N c)) / ((Module.finrank ℚ K : ℝ) * (Fintype.card γ * r)) := by
    have := (Formalism.HN.plLat K A.V A.ι A.b A.X hA _ hfT).2.1
    show Formalism.HN.deg (realize A.b A.X) (⨆ c, N c) / ((Formalism.HN.rk (realize A.b A.X) (⨆ c, N c) : ℕ) : ℝ) = _
    rw [this, hrkT, h1]
    push_cast
    rfl
  constructor
  · show Formalism.HN.muDef A.b A.X (⨆ c, N c) = mean fun c => Formalism.HN.muDef A.b A.X (N c)
    unfold Formalism.HN.muDef mean
    rw [hslT]
    simp only [hsl]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    field_simp
  · obtain ⟨c, -, hc⟩ := Finset.exists_max_image (Finset.univ : Finset γ)
      (fun c => Formalism.HN.muMax (realize A.b A.X) (N c)) Finset.univ_nonempty
    refine ⟨c, ?_⟩
    show Formalism.HN.muMaxDef A.b A.X (⨆ c, N c) ≤ Formalism.HN.muMaxDef A.b A.X (N c)
    unfold Formalism.HN.muMaxDef
    have := (h2 Finset.univ_nonempty).2 _ hc
    linarith

end Orth

section GSDOrth

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) (hf : S.Free)

open Classical in

def GSD.extZ (c : S.Cl) : S.V →ₗ[K] S.EqFun :=
  (S.resFree h S.outSec hf).symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : S.Cl => S.V) c

open Classical in
theorem GSD.extZ_apply (c c' : S.Cl) (x : S.V) :
    ((S.extZ h hf c x : S.EqFun) : S.D → S.V) (S.outSec.rep c') = if c' = c then x else 0 := by
  have h1 := congrFun ((S.resFree h S.outSec hf).apply_symm_apply (Pi.single c x)) c'
  rw [GSD.resFree_apply] at h1
  rw [Pi.single_apply] at h1
  exact h1

theorem GSD.extZ_injective (c : S.Cl) : Function.Injective (S.extZ h hf c) := by
  classical
  intro x y hxy
  have h1 := S.extZ_apply h hf c c x
  have h2 := S.extZ_apply h hf c c y
  rw [if_pos rfl] at h1 h2
  rw [← h1, ← h2, hxy]

theorem GSD.brzo_pairAt_zero_left (v : InfinitePlace K) (y : S.V) : S.pairAt v 0 y = 0 := by
  simp [GSD.pairAt]

theorem GSD.brzo_pairAt_zero_right (v : InfinitePlace K) (x : S.V) : S.pairAt v x 0 = 0 := by
  simp [GSD.pairAt]

open Classical in

theorem GSD.ipAt_extZ (v : InfinitePlace K) (c c' : S.Cl) (x y : S.V) :
    S.ipAt h v (S.extZ h hf c x) (S.extZ h hf c' y) = if c = c' then S.pairAt v x y else 0 := by
  unfold GSD.ipAt
  simp only [S.extZ_apply h hf, S.wt_eq_one h S.outSec hf, Nat.cast_one, inv_one, one_mul]
  let _ : Fintype S.Cl := h.fintypeCl
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl]
    split_ifs with hc
    · rfl
    · exact S.brzo_pairAt_zero_right v x
  · intro b _ hb
    rw [if_neg hb]
    exact S.brzo_pairAt_zero_left v _
  · intro hc
    exact absurd (Finset.mem_univ _) hc

def GSD.extL (c : S.Cl) : Submodule (𝓞 K) S.EqFun :=
  (S.Del (S.outSec.rep c)).map ((S.extZ h hf c).restrictScalars (𝓞 K))

theorem GSD.iSup_extL : (⨆ c, S.extL h hf c) = S.intDel := by
  classical
  have : Finite S.Cl := h.fin_orb
  have e1 : S.intDel = (Submodule.pi Set.univ fun c => S.Del (S.outSec.rep c)).map
      (((S.resFree h S.outSec hf).symm : (S.Cl → S.V) →ₗ[K] S.EqFun).restrictScalars (𝓞 K)) := by
    rw [← S.map_intDel_free h S.outSec hf, ← Submodule.map_comp]
    have : (((S.resFree h S.outSec hf).symm : (S.Cl → S.V) →ₗ[K] S.EqFun).restrictScalars (𝓞 K)) ∘ₗ
        ((S.resFree h S.outSec hf : S.EqFun →ₗ[K] (S.Cl → S.V)).restrictScalars (𝓞 K)) = LinearMap.id := by
      ext1 φ
      exact (S.resFree h S.outSec hf).symm_apply_apply φ
    rw [this, Submodule.map_id]
  rw [e1, ← Submodule.iSup_map_single, Submodule.map_iSup]
  refine iSup_congr fun c => ?_
  rw [← Submodule.map_comp]
  rfl

end GSDOrth

section GSDOrth2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

theorem GSD.orth_of_free (h : S.Ok) (hf : S.Free) [Nontrivial S.V] [Nonempty S.Cl] (R : S.Rat) (hD : ∀ d, Submodule.IsLattice K (S.Del d)) :
    S.OrthMean h ∧ S.OrthMax h := by
  classical
  let _ : Fintype S.Cl := h.fintypeCl
  have hfin : Module.Finite K S.V := Module.Finite.of_basis S.bV
  have hA : FrameOK (S.toH h S.intDel) := (R.posH h).frameOK _
  have hmaj : ∀ v (φ ψ : S.EqFun), majAt (S.toH h S.intDel).b (S.toH h S.intDel).X v φ ψ = S.ipAt h v φ ψ :=
    fun v φ ψ => R.maj_eq h v φ ψ
  have hnorm : ∀ c v (x : S.V), normAt (S.valH (S.outSec.rep c)).b (S.valH (S.outSec.rep c)).X v x =
      normAt (S.toH h S.intDel).b (S.toH h S.intDel).X v (S.extZ h hf c x) := by
    intro c v x
    rw [(GSD.valH_spec R (S.outSec.rep c)).2.2 v x, normAt_eq_sqrt, hmaj, S.ipAt_extZ h hf, if_pos rfl]
  have hnum := fun c => (emb_numbers K (S.valH (S.outSec.rep c)) (S.toH h S.intDel) (S.extZ h hf c) hA
    (S.extZ_injective h hf c) (hnorm c)).2 (S.Del (S.outSec.rep c))
  have hrk : ∀ c, Formalism.HN.rkK (S.extL h hf c) = finrank K S.V := by
    intro c
    unfold GSD.extL
    rw [rkK_map _ (S.extZ_injective h hf c)]
    unfold Formalism.HN.rkK
    rw [(hD _).span_eq_top, finrank_top]
  have hr : 0 < finrank K S.V := Module.finrank_pos
  have hne : ∀ c, S.extL h hf c ≠ ⊥ := by
    intro c h0
    have h1 := hrk c
    rw [h0] at h1
    have h2 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) S.EqFun) = 0 := by
      unfold Formalism.HN.rkK
      rw [Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot]
    omega
  have hrkT : Formalism.HN.rkK (⨆ c, S.extL h hf c) = Fintype.card S.Cl * finrank K S.V := by
    rw [S.iSup_extL h hf]
    unfold Formalism.HN.rkK
    rw [(S.intDel_isLattice h hD).span_eq_top, finrank_top, S.finrank_free h hf, Nat.card_eq_fintype_card]
  have key := hlat_orth_sum (A := S.toH h S.intDel) (S.extL h hf) hA (fun c => (hD _).fg.map _) hne
    (by
      intro c c' hcc x hx y hy v
      obtain ⟨x', -, rfl⟩ := hx
      obtain ⟨y', -, rfl⟩ := hy
      exact (hmaj v _ _).trans ((S.ipAt_extZ h hf v c c' x' y').trans (if_neg hcc)))
    (finrank K S.V) hr hrk hrkT
  rw [S.iSup_extL h hf] at key
  constructor
  · refine key.1.trans ?_
    congr 1
    funext c
    exact (((hnum c).2 (hD _).fg).1).symm
  · obtain ⟨c, hc⟩ := key.2
    exact ⟨c, hc.trans (le_of_eq (((hnum c).2 (hD _).fg).2.1).symm)⟩

end GSDOrth2

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem col_orthMean (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    (colGSD W Ch u 0).OrthMean (colOk W Ch hX u 0) :=
  haveI := colCl_nonempty W Ch u
  haveI : Nontrivial (colGSD W Ch u 0).V := (colVal W u 0 (Pr.vT u) Pr.vGs).V_nontrivial
  (GSD.orth_of_free (colOk W Ch hX u 0) (colFree W Ch hX hPr hbig u) (colRat W Ch hX u 0) (thl_colDel_isLattice W Ch u 0)).1

theorem col_orthMax (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    (colGSD W Ch u 0).OrthMax (colOk W Ch hX u 0) :=
  haveI := colCl_nonempty W Ch u
  haveI : Nontrivial (colGSD W Ch u 0).V := (colVal W u 0 (Pr.vT u) Pr.vGs).V_nontrivial
  (GSD.orth_of_free (colOk W Ch hX u 0) (colFree W Ch hX hPr hbig u) (colRat W Ch hX u 0) (thl_colDel_isLattice W Ch u 0)).2

end Cols

theorem propZ_col' : ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (hX : X.Ok) (_ : Pr.Ok) (_ : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (a b' L eta S : ℝ),
    NumbersC Pr R u C₀ a b' L eta S → WtWin W u C₀ a b' S → SummandSlopeAtDecoratedLattice W Ch u → MaxSlopeSummandWithConstant W Ch u C₀ →
    (∀ τ, DualSlope X.K (W.lamTrue u 0 τ)) → (∀ τ, MaxSlopeNablaBound X.K (kap_succ R) (W.lamTrue u 0 τ)) →
    ZiiC W u C a b' L S ≤ (Mu0H W Ch hX u).mu ∧ (Mu0H W Ch hX u).muMax ≤ ZiiiC W u C a b' L S := by
  intro C₀ h0
  obtain ⟨C, hC0, hC⟩ := propZ_col C₀ h0
  exact ⟨C, hC0, fun W Ch hX hPr hbig u a b' L eta S hN hW h5 h5' hD h4 =>
    hC W Ch hX u a b' L eta S hN hW (col_orthMean W Ch hX hPr hbig u) (col_orthMax W Ch hX hPr hbig u) h5 h5' hD
      (fun τ => slopeLeMax _ _) h4⟩

end Formalism.L2.Col
