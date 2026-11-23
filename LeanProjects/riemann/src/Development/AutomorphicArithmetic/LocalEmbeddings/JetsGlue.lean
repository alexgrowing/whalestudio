import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.JetsChain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.JetsOne

variable {D : D7}

section Last

variable {A A' : HSp D} {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
  (ρ : GA D A →* Module.End ℂ M) (Λ : Module.Dual ℂ M) (ρ' : GA D A' →* Module.End ℂ M') (Λ' : Module.Dual ℂ M')
  (s : GA D A' →* GA D A) (e : GfC A' → GfC A) (B : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ)

structure LastOK : Prop where

  defn : IsDefiniteSpace A'

  pos : ∀ φ : D.host.E →+* ℂ, (A'.gram.map φ).PosDef

  fin : ∀ g ∈ GfC A, ρ g = 1

  fin' : ∀ g ∈ GfC A', ρ' g = 1

  cont : Continuous s

  rat : ∀ γ ∈ GQ A', s γ ∈ GQ A

  sfin : ∀ z : GfC A', s z = e z

  sinf : ∀ k ∈ GinfC A', s k ∈ GinfC A

  coef : ∀ u u', Continuous fun k : GinfC A' => Λ (ρ (s k)⁻¹ u) * Λ' (ρ' (k : GA D A')⁻¹ u')

  avg : ∀ κ : Measure (GinfC A'), κ.IsHaarMeasure → IsProbabilityMeasure κ → ∀ u u',
    ∫ k, Λ (ρ (s k)⁻¹ u) * Λ' (ρ' (k : GA D A')⁻¹ u') ∂κ = B u u'

variable {ρ Λ ρ' Λ' s e B} (h : LastOK ρ Λ ρ' Λ' s e B) {F : GA D A → ℂ} {F' : GA D A' → ℂ} {v : GfC A → M} {v' : GfC A' → M'}
  (hF : IsFinReal ρ F Λ v) (hF' : IsFinReal ρ' F' Λ' v')
include h hF hF'

theorem last_avg (κ : Measure (GinfC A')) (h1 : κ.IsHaarMeasure) (h2 : IsProbabilityMeasure κ) (z : GfC A') :
    ∫ k, F (s (z * k)) * F' (z * k) ∂κ = B (v (e z)) (v' z) := by
  rw [← h.avg κ h1 h2]
  refine integral_congr_ae (.of_forall fun k => ?_)
  have e1 := isFinReal_apply h.fin hF (e z) ⟨s k, h.sinf _ k.2⟩
  beta_reduce
  rw [map_mul, h.sfin, isFinReal_apply h.fin' hF']
  exact congrArg (· * _) e1

theorem last_int (hFa : ∀ γ ∈ GQ A, ∀ g, F (γ * g) = F g) (hFa' : ∀ γ ∈ GQ A', ∀ g, F' (γ * g) = F' g)
    {K K₀ : Subgroup (GL (Fin A'.rank) (Lev.EAf D))} (hK : IsOpenCompactLevel _ K) (hK₀ : IsOpenCompactLevel _ K₀) (hle : K ≤ K₀)
    {μ : Measure (GA D A')} {fd : Set (GA D A')} (hμ : IsMeasDef _ K₀ μ fd)
    (hr : ∀ k ∈ Lev.levA _ K, (∀ g, F (g * s k) = F g) ∧ ∀ g, F' (g * k) = F' g) :
    ∫ g in fd, F (s g) * F' g ∂μ = ∑ᶠ c : FinCl A' K, wgt A' μ K c * B (v (e (Quotient.out c))) (v' (Quotient.out c)) := by
  obtain ⟨hfin, κ, hκH, hκP, hU⟩ := GlobalTheory.DefiniteClassReal.integral_eq_finClSum_avg A' h.pos K₀ K hK₀ hK hle μ fd hμ
    (fun g => F (s g) * F' g)
    (fun γ hγ g => by rw [map_mul, hFa _ (h.rat γ hγ), hFa' γ hγ])
    (fun k hk g => by rw [map_mul, (hr k hk).1, (hr k hk).2])
    (fun z => by
      have e1 : ∀ k : GinfC A', F (s (z * k)) = Λ (ρ (s k)⁻¹ (ρ (s z)⁻¹ (v (finOf _ (s z))))) := fun k => by
        rw [hF, map_mul, finOf_mul_inf _ _ ⟨s k, h.sinf _ k.2⟩, mul_inv_rev, map_mul, Module.End.mul_apply]
      have e2 : ∀ k : GinfC A', F' (z * k) = Λ' (ρ' (k : GA D A')⁻¹ (ρ' z⁻¹ (v' (finOf _ z)))) := fun k => by
        rw [hF', finOf_mul_inf, mul_inv_rev, map_mul, Module.End.mul_apply]
      simp only [e1, e2]
      exact h.coef _ _)
  rw [hU]
  refine finsum_congr fun c => ?_
  rw [last_avg h hF hF' κ hκH hκP, wgt, div_eq_mul_inv]

end Last

section Sums

variable {V : ℕ → HSp D} {Mo : ℕ → Type} [∀ n, AddCommGroup (Mo n)] [∀ n, Module ℂ (Mo n)]
  (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0)

theorem ext_lt {P : ℕ → Type} [∀ j, One (P j)] {n : ℕ} (x : ∀ j : Fin n, P j) {j : ℕ} (h : j < n) : ext n x j = x ⟨j, h⟩ :=
  dif_pos h

theorem ext_update {P : ℕ → Type} [∀ j, One (P j)] {n : ℕ} (x : ∀ j : Fin n, P j) (j : Fin n) (z : P j) :
    ext n (Function.update (β := fun j : Fin n => P j) x j z) = Function.update (β := P) (ext n x) (j : ℕ) z := by
  funext i
  by_cases hi : i = j
  · subst hi
    rw [ext_lt _ j.2, Function.update_self]
    exact (Function.update_self (β := P) (j : ℕ) z _).symm
  · rw [Function.update_of_ne hi]
    unfold ext
    split_ifs with h
    · exact Function.update_of_ne (fun e => hi (congrArg Fin.val e)) _ _
    · rfl

theorem sum_last {A : ℕ → Type} (o : ∀ n, A n → GfC (V n)) (w : ∀ n, A n → ℂ) (n : ℕ) (hA : ∀ j < n + 1, Finite (A j))
    (ℓ : GfC (V n) → Mo n →ₗ[ℂ] ℂ) :
    ∑ᶠ a : A n, w n a * ℓ (o n a) (sumV o w comp v n (o n a)) =
      ∑ᶠ c : (∀ j : Fin (n + 1), A j), (∏ j : Fin (n + 1), w j (c j)) *
        ℓ (ext (P := fun j => GfC (V j)) (n + 1) (fun j => o j (c j)) n)
          (ptV comp v (ext (n + 1) fun j => o j (c j)) n (ext (P := fun j => GfC (V j)) (n + 1) (fun j => o j (c j)) n)) := by
  rw [finsum_snoc n hA]
  refine finsum_congr fun a => ?_
  letI : ∀ j : Fin n, Fintype (A j) := fun j => @Fintype.ofFinite _ (hA j (by omega))
  rw [sumV_eq comp v o w n fun j hj => hA j (by omega), finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : ext (P := fun j => GfC (V j)) (n + 1)
      (fun j => o j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j)) n = o n a := by
    rw [ext, dif_pos (Nat.lt_succ_self n)]
    exact congrArg (o n) (Fin.snoc_last (α := fun j : Fin (n + 1) => A j) a c)
  have e2 : ptV comp v (ext (n + 1) fun j => o j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j)) n =
      ptV comp v (ext n fun j => o j (c j)) n := ptV_congr comp v n fun j hj => by
    rw [ext, ext, dif_pos (Nat.lt_succ_of_lt hj), dif_pos hj]
    exact congrArg (o j) (Fin.snoc_castSucc (α := fun j : Fin (n + 1) => A j) a c ⟨j, hj⟩)
  have e3 : ∏ j : Fin (n + 1), w j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j) = w n a * ∏ j : Fin n, w j (c j) := by
    rw [Fin.prod_univ_castSucc, mul_comm]
    refine congrArg₂ _ (congrArg (w n) (Fin.snoc_last (α := fun j : Fin (n + 1) => A j) a c)) ?_
    exact Finset.prod_congr rfl fun j _ => congrArg (w j) (Fin.snoc_castSucc (α := fun j : Fin (n + 1) => A j) a c j)
  rw [e1, e2, e3, map_smul, smul_eq_mul, mul_assoc]

end Sums

section Glue

variable {V V' : ℕ → HSp D} {Mo Mo' : ℕ → Type} [∀ n, AddCommGroup (Mo n)] [∀ n, Module ℂ (Mo n)]
  [∀ n, AddCommGroup (Mo' n)] [∀ n, Module ℂ (Mo' n)]

def pairP (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0)
    (comp' : ∀ n, GfC (V' n) → GfC (V' (n + 1)) → Mo' n →ₗ[ℂ] Mo' (n + 1)) (v' : GfC (V' 0) → Mo' 0) (N : ℕ)
    (B : Mo N →ₗ[ℂ] Mo' N →ₗ[ℂ] ℂ) (X : ∀ n, GfC (V n)) (Y : ∀ n, GfC (V' n)) : ℂ :=
  B (ptV comp v X N (X N)) (ptV comp' v' Y N (Y N))

def ptX (N : ℕ) (e : GfC (V' N) → GfC (V N)) (x : ∀ j : Fin N, GfC (V j)) (y : ∀ i : Fin (N + 1), GfC (V' i)) : ∀ j, GfC (V j) :=
  Function.update (ext (P := fun j => GfC (V j)) N x) N (e (ext (P := fun j => GfC (V' j)) (N + 1) y N))

variable {comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)} {v : GfC (V 0) → Mo 0}
  {comp' : ∀ n, GfC (V' n) → GfC (V' (n + 1)) → Mo' n →ₗ[ℂ] Mo' (n + 1)} {v' : GfC (V' 0) → Mo' 0}
  {ρ : ∀ n, GA D (V n) →* Module.End ℂ (Mo n)} {ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ} {Λ : ∀ n, Module.Dual ℂ (Mo n)}
  {ρ' : ∀ n, GA D (V' n) →* Module.End ℂ (Mo' n)} {ker' : ∀ n, GA D (V' n) → GA D (V' (n + 1)) → ℂ}
  {Λ' : ∀ n, Module.Dual ℂ (Mo' n)} {N : ℕ} {s : GA D (V' N) →* GA D (V N)} {e : GfC (V' N) → GfC (V N)}
  {B : Mo N →ₗ[ℂ] Mo' N →ₗ[ℂ] ℂ}
  (hc : ∀ n < N, ArrowOK comp ρ ker Λ n) {F : GA D (V 0) → ℂ} (hF : IsFinReal (ρ 0) F (Λ 0) v)
  (hFa : ∀ γ ∈ GQ (V 0), ∀ g, F (γ * g) = F g)
  (hc' : ∀ n < N, ArrowOK comp' ρ' ker' Λ' n) {F' : GA D (V' 0) → ℂ} (hF' : IsFinReal (ρ' 0) F' (Λ' 0) v')
  (hFa' : ∀ γ ∈ GQ (V' 0), ∀ g, F' (γ * g) = F' g)
  (h : LastOK (ρ N) (Λ N) (ρ' N) (Λ' N) s e B)
include hc hF hFa hc' hF' hFa' h

theorem pairP_rat {X X' : ∀ n, GfC (V n)} {Y Y' : ∀ n, GfC (V' n)} (hX : ∀ j < N, ∃ γ ∈ ratFin (V j), X' j = γ * X j)
    (hY : ∀ j ≤ N, ∃ γ ∈ ratFin (V' j), Y' j = γ * Y j) (h1 : X N = e (Y N)) (h2 : X' N = e (Y' N)) :
    pairP comp v comp' v' N B X' Y' = pairP comp v comp' v' N B X Y := by
  obtain ⟨κ, k1, k2⟩ := exists_haar _ h.defn
  obtain ⟨γ, hγ, e3⟩ := hY N le_rfl
  rw [pairP, pairP, h1, h2, ← last_avg h (ptF_real comp v ρ Λ X' N) (ptF_real comp' v' ρ' Λ' Y' N) κ k1 k2,
    ← last_avg h (ptF_real comp v ρ Λ X N) (ptF_real comp' v' ρ' Λ' Y N) κ k1 k2, ptF_rat hc hF hFa hX N le_rfl,
    ptF_rat hc' hF' hFa' (fun j hj => hY j hj.le) N le_rfl, e3]
  exact avg_rat _ κ (fun z => ptF comp v ρ Λ X N (s z) * ptF comp' v' ρ' Λ' Y N z) (fun q hq z => by
    rw [map_mul, ptF_left hc hF hFa X N le_rfl _ (h.rat q hq), ptF_left hc' hF' hFa' Y N le_rfl q hq]) hγ _

theorem one_term (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n)))
    (K : ∀ n, Subgroup (GL (Fin (V n).rank) (Lev.EAf D)))
    (hK : ∀ n < N, IsOpenCompactLevel _ (K n) ∧ (∃ K₀, IsOpenCompactLevel _ K₀ ∧ K n ≤ K₀ ∧ IsMeasDef _ K₀ (μ n) (fd n)) ∧
      ∀ k ∈ Lev.levA _ (K n), FixAt ker F n k ∧ ∀ g h, ker n (g * k) h = ker n g h)
    (μ' : ∀ n, Measure (GA D (V' n))) (fd' : ∀ n, Set (GA D (V' n)))
    (K' : ∀ n, Subgroup (GL (Fin (V' n).rank) (Lev.EAf D)))
    (hK' : ∀ n < N, IsOpenCompactLevel _ (K' n) ∧ (∃ K₀, IsOpenCompactLevel _ K₀ ∧ K' n ≤ K₀ ∧ IsMeasDef _ K₀ (μ' n) (fd' n)) ∧
      ∀ k ∈ Lev.levA _ (K' n), FixAt ker' F' n k ∧ ∀ g h, ker' n (g * k) h = ker' n g h)
    (hN : IsOpenCompactLevel _ (K' N) ∧ (∃ K₀, IsOpenCompactLevel _ K₀ ∧ K' N ≤ K₀ ∧ IsMeasDef _ K₀ (μ' N) (fd' N)) ∧
      ∀ k ∈ Lev.levA _ (K' N), FixAt ker F N (s k) ∧ FixAt ker' F' N k) :
    ∫ g in fd' N, liftC μ fd ker F N (s g) * liftC μ' fd' ker' F' N g ∂μ' N =
      ∑ᶠ c : (∀ j : Fin N, FinCl (V j) (K j)) × (∀ i : Fin (N + 1), FinCl (V' i) (K' i)),
        ((∏ j : Fin N, wgt (V j) (μ j) (K j) (c.1 j)) * ∏ i : Fin (N + 1), wgt (V' i) (μ' i) (K' i) (c.2 i)) *
          pairP comp v comp' v' N B (ptX N e (fun j => Quotient.out (c.1 j)) (fun i => Quotient.out (c.2 i)))
            (ext (P := fun j => GfC (V' j)) (N + 1) fun i => Quotient.out (c.2 i)) := by
  obtain ⟨n1, ⟨K₀, n2, n3, n4⟩, n5⟩ := hN
  have fA : ∀ j < N, Finite (FinCl (V j) (K j)) := fun j hj =>
    (ClassFin.finite_finCl_and_gamOrd _ _ (hc j hj).2.1 (hK j hj).1).1
  have fA' : ∀ j < N + 1, Finite (FinCl (V' j) (K' j)) := fun j hj => by
    rcases (Nat.lt_succ_iff.1 hj).eq_or_lt with rfl | hj
    · exact (ClassFin.finite_finCl_and_gamOrd _ _ h.pos n1).1
    · exact (ClassFin.finite_finCl_and_gamOrd _ _ (hc' j hj).2.1 (hK' j hj).1).1
  rw [last_int h (liftC_real hc hF hFa μ fd K hK N le_rfl) (liftC_real hc' hF' hFa' μ' fd' K' hK' N le_rfl)
    (liftC_left hc hFa μ fd N le_rfl) (liftC_left hc' hFa' μ' fd' N le_rfl) n1 n2 n3 n4
    (fun k hk => ⟨liftC_right μ fd N _ (n5 k hk).1, liftC_right μ' fd' N _ (n5 k hk).2⟩)]
  refine (sum_last comp' v' (A := fun n => FinCl (V' n) (K' n)) (fun _ c => Quotient.out c) (fun n => wgt (V' n) (μ' n) (K' n)) N fA'
    (fun z => B (sumV (A := fun n => FinCl (V n) (K n)) (fun _ c => Quotient.out c) (fun n => wgt (V n) (μ n) (K n))
      comp v N (e z)))).trans ?_
  letI : ∀ j : Fin N, Fintype (FinCl (V j) (K j)) := fun j => @Fintype.ofFinite _ (fA j j.2)
  letI : ∀ j : Fin (N + 1), Fintype (FinCl (V' j) (K' j)) := fun j => @Fintype.ofFinite _ (fA' j j.2)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sumV_eq comp v _ _ N fA, finsum_eq_sum_of_fintype, map_sum, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e1 : ptV comp v (ptX N e (fun j => Quotient.out (a j)) (fun i => Quotient.out (b i))) N =
      ptV comp v (ext N fun j => Quotient.out (a j)) N := ptV_congr comp v N fun j hj => Function.update_of_ne hj.ne _ _
  have e2 : ptX N e (fun j => Quotient.out (a j)) (fun i => Quotient.out (b i)) N =
      e (ext (P := fun j => GfC (V' j)) (N + 1) (fun i => Quotient.out (b i)) N) := Function.update_self ..
  rw [pairP, e1, e2, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

end Glue

section Total

variable {V V' : ℕ → HSp D} {Mo Mo' : ℕ → Type} [∀ n, AddCommGroup (Mo n)] [∀ n, Module ℂ (Mo n)]
  [∀ n, AddCommGroup (Mo' n)] [∀ n, Module ℂ (Mo' n)]

def NearOK (ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ) (F : GA D (V 0) → ℂ) (N : ℕ) : Prop :=
  (∀ᶠ k in 𝓝 (1 : GA D (V 0)), k ∈ GfC (V 0) → ∀ g, F (g * k) = F g) ∧
  ∀ n < N, (∀ᶠ k in 𝓝 (1 : GA D (V n)), k ∈ GfC (V n) → ∀ g h, ker n (g * k) h = ker n g h) ∧
    ∀ᶠ k in 𝓝 (1 : GA D (V (n + 1))), k ∈ GfC (V (n + 1)) → ∀ g h, ker n g (h * k) = ker n g h

theorem NearOK.fixAt {ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ} {F : GA D (V 0) → ℂ} {N : ℕ} (h : NearOK ker F N) :
    ∀ n ≤ N, ∀ᶠ k in 𝓝 (1 : GA D (V n)), k ∈ GfC (V n) → FixAt ker F n k
  | 0, _ => h.1
  | n + 1, hn => (h.2 n hn).2

theorem exists_fine_chain {ι : Type} (S : Finset ι) {ker : ι → ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ} {F : GA D (V 0) → ℂ} {N : ℕ}
    (h : ∀ d ∈ S, NearOK (ker d) F N) {n : ℕ} (hn : n < N) {K : Subgroup (GL (Fin (V n).rank) (Lev.EAf D))}
    (hK : IsOpenCompactLevel _ K) : ∃ K'' ≤ K, IsOpenCompactLevel _ K'' ∧ ∀ k ∈ Lev.levA _ K'', ∀ d ∈ S,
      FixAt (ker d) F n k ∧ ∀ g h, ker d n (g * k) h = ker d n g h := by
  refine exists_fine _ hK ?_
  have := (Filter.eventually_all_finset S).2 fun d hd => ((h d hd).fixAt n hn.le).and ((h d hd).2 n hn).1
  exact this.mono fun k hk hf d hd => ⟨(hk d hd).1 hf, (hk d hd).2 hf⟩

variable {ι : Type} (τ : ι →₀ ℂ)
  {comp : ι → ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)} {v : GfC (V 0) → Mo 0}
  {comp' : ι → ∀ n, GfC (V' n) → GfC (V' (n + 1)) → Mo' n →ₗ[ℂ] Mo' (n + 1)} {v' : GfC (V' 0) → Mo' 0}
  {ρ : ∀ n, GA D (V n) →* Module.End ℂ (Mo n)} {ker : ι → ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ} {Λ : ∀ n, Module.Dual ℂ (Mo n)}
  {ρ' : ∀ n, GA D (V' n) →* Module.End ℂ (Mo' n)} {ker' : ι → ∀ n, GA D (V' n) → GA D (V' (n + 1)) → ℂ}
  {Λ' : ∀ n, Module.Dual ℂ (Mo' n)} {N : ℕ} {s : GA D (V' N) →* GA D (V N)} {e : GfC (V' N) → GfC (V N)}
  {B : Mo N →ₗ[ℂ] Mo' N →ₗ[ℂ] ℂ} {F : GA D (V 0) → ℂ} {F' : GA D (V' 0) → ℂ}

theorem glue (hc : ∀ d ∈ τ.support, ∀ n < N, ArrowOK (comp d) ρ (ker d) Λ n) (hF : IsFinReal (ρ 0) F (Λ 0) v)
    (hFa : ∀ γ ∈ GQ (V 0), ∀ g, F (γ * g) = F g) (hn : ∀ d ∈ τ.support, NearOK (ker d) F N)
    (hc' : ∀ d ∈ τ.support, ∀ n < N, ArrowOK (comp' d) ρ' (ker' d) Λ' n) (hF' : IsFinReal (ρ' 0) F' (Λ' 0) v')
    (hFa' : ∀ γ ∈ GQ (V' 0), ∀ g, F' (γ * g) = F' g) (hn' : ∀ d ∈ τ.support, NearOK (ker' d) F' N)
    (h : LastOK (ρ N) (Λ N) (ρ' N) (Λ' N) s e B)
    (hV : ∀ n < N, ∀ φ : D.host.E →+* ℂ, ((V n).gram.map φ).PosDef)
    (hV' : ∀ n ≤ N, ∀ φ : D.host.E →+* ℂ, ((V' n).gram.map φ).PosDef)
    (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n))) (K : ∀ n, n < N → Subgroup (GL (Fin (V n).rank) (Lev.EAf D)))
    (hK : ∀ n hn, IsOpenCompactLevel _ (K n hn) ∧ IsMeasDef _ (K n hn) (μ n) (fd n))
    (μ' : ∀ n, Measure (GA D (V' n))) (fd' : ∀ n, Set (GA D (V' n))) (K' : ∀ n, n ≤ N → Subgroup (GL (Fin (V' n).rank) (Lev.EAf D)))
    (hK' : ∀ n hn, IsOpenCompactLevel _ (K' n hn) ∧ IsMeasDef _ (K' n hn) (μ' n) (fd' n))
    (P : (∀ n, GfC (V n)) → (∀ n, GfC (V' n)) → ℂ)
    (hP : ∀ X Y, P X Y = τ.sum fun d a => a * pairP (comp d) v (comp' d) v' N B X Y)
    (r1 : ∀ X Y j (hj : j < N) k, finG (V j) k ∈ K j hj → P (Function.update X j (X j * k)) Y = P X Y)
    (r2 : ∀ X Y i (hi : i < N) k, finG (V' i) k ∈ K' i hi.le → P X (Function.update Y i (Y i * k)) = P X Y)
    (r3 : ∀ X Y k, X N = e (Y N) → finG (V' N) k ∈ K' N le_rfl →
      P (Function.update X N (e (Y N * k))) (Function.update Y N (Y N * k)) = P X Y) :
    (τ.sum fun d a => a * ∫ g in fd' N, liftC μ fd (ker d) F N (s g) * liftC μ' fd' (ker' d) F' N g ∂μ' N) =
      ∑ᶠ c : (∀ j : Fin N, FinCl (V j) (K j j.2)) × (∀ i : Fin (N + 1), FinCl (V' i) (K' i (Nat.le_of_lt_succ i.2))),
        ((∏ j : Fin N, ((gamOrd (V j) (K j j.2) (Quotient.out (c.1 j)) : ℂ))⁻¹) *
          ∏ i : Fin (N + 1), ((gamOrd (V' i) (K' i (Nat.le_of_lt_succ i.2)) (Quotient.out (c.2 i)) : ℂ))⁻¹) *
          P (ptX N e (fun j => Quotient.out (c.1 j)) (fun i => Quotient.out (c.2 i)))
            (ext (P := fun j => GfC (V' j)) (N + 1) fun i => Quotient.out (c.2 i)) := by
  have hG := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (V N)).2.2.2.2.1
  have hG' := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (V' N)).2.2.2.2.1
  have x1 : ∀ n, ∃ K'' : Subgroup (GL (Fin (V n).rank) (Lev.EAf D)), ∀ hn : n < N, K'' ≤ K n hn ∧ IsOpenCompactLevel _ K'' ∧
      ∀ k ∈ Lev.levA _ K'', ∀ d ∈ τ.support, FixAt (ker d) F n k ∧ ∀ g h, ker d n (g * k) h = ker d n g h := fun n => by
    by_cases h0 : n < N
    · obtain ⟨K'', a⟩ := exists_fine_chain τ.support hn h0 (hK n h0).1
      exact ⟨K'', fun _ => a⟩
    · exact ⟨⊤, fun h1 => absurd h1 h0⟩
  have x2 : ∀ n, ∃ K'' : Subgroup (GL (Fin (V' n).rank) (Lev.EAf D)), ∀ hn : n ≤ N, K'' ≤ K' n hn ∧ IsOpenCompactLevel _ K'' ∧
      (n < N → ∀ k ∈ Lev.levA _ K'', ∀ d ∈ τ.support, FixAt (ker' d) F' n k ∧ ∀ g h, ker' d n (g * k) h = ker' d n g h) ∧
      ∀ hN : n = N, ∀ k ∈ Lev.levA _ K'', ∀ d ∈ τ.support, FixAt (ker d) F N (s (hN ▸ k)) ∧ FixAt (ker' d) F' n k := fun n => by
    rcases lt_trichotomy n N with h0 | rfl | h0
    · obtain ⟨K'', a, b, c⟩ := exists_fine_chain τ.support hn' h0 (hK' n h0.le).1
      exact ⟨K'', fun _ => ⟨a, b, fun _ => c, fun e => absurd e h0.ne⟩⟩
    · have t : Filter.Tendsto s (𝓝 1) (𝓝 1) := by simpa using h.cont.tendsto 1
      have := (Filter.eventually_all_finset τ.support).2 fun d hd =>
        (t.eventually ((hn d hd).fixAt n le_rfl)).and ((hn' d hd).fixAt n le_rfl)
      obtain ⟨K'', a, b, c⟩ := exists_fine _ (hK' n le_rfl).1
        (p := fun k => ∀ d ∈ τ.support, FixAt (ker d) F n (s k) ∧ FixAt (ker' d) F' n k)
        (this.mono fun k hk hf d hd => ⟨(hk d hd).1 (by rw [h.sfin ⟨k, hf⟩]; exact (e _).2), (hk d hd).2 hf⟩)
      exact ⟨K'', fun _ => ⟨a, b, fun e => absurd e (lt_irrefl _), fun _ => c⟩⟩
    · exact ⟨⊤, fun h1 => absurd h0 (not_lt.2 h1)⟩
  choose J hJ using x1
  choose J' hJ' using x2
  have hrat : ∀ {X X' : ∀ n, GfC (V n)} {Y Y' : ∀ n, GfC (V' n)}, (∀ j < N, ∃ γ ∈ ratFin (V j), X' j = γ * X j) →
      (∀ j ≤ N, ∃ γ ∈ ratFin (V' j), Y' j = γ * Y j) → X N = e (Y N) → X' N = e (Y' N) → P X' Y' = P X Y :=
    fun a1 a2 a3 a4 => by
      rw [hP, hP]
      exact Finsupp.sum_congr fun d hd => by rw [pairP_rat (hc d hd) hF hFa (hc' d hd) hF' hFa' h a1 a2 a3 a4]
  have up : ∀ {W : ℕ → HSp D} (X : ∀ n, GfC (W n)) (j : ℕ) (γ : GfC (W j)), γ ∈ ratFin (W j) → ∀ (z : GfC (W j)) (i : ℕ),
      ∃ γ' ∈ ratFin (W i), Function.update X j (γ * z) i = γ' * Function.update X j z i := fun X j γ hγ z i => by
    by_cases hi : i = j
    · subst hi
      exact ⟨γ, hγ, by simp⟩
    · exact ⟨1, one_mem _, by simp [Function.update_of_ne hi]⟩
  have pN : ∀ x y, ptX (V := V) (V' := V') N e x y N = e (ext (P := fun j => GfC (V' j)) (N + 1) y N) := fun x y =>
    Function.update_self ..
  have pU : ∀ x y (j : Fin N) z, ptX (V := V) (V' := V') N e (Function.update (β := fun j : Fin N => GfC (V j)) x j z) y =
      Function.update (β := fun j => GfC (V j)) (ptX N e x y) (j : ℕ) z := fun x y j z => by
    rw [ptX, ptX, ext_update (P := fun j => GfC (V j)), Function.update_comm j.2.ne]
  rw [← GlobalTheory.ClassRegroup.finCl_regroup_prod (fun j : Fin N => V j) (fun i : Fin (N + 1) => V' i) (fun j => hV j j.2)
    (fun i => hV' i (Nat.le_of_lt_succ i.2)) (K := fun j => K j j.2) (K'' := fun j => J j)
    (L := fun i => K' i (Nat.le_of_lt_succ i.2)) (L'' := fun i => J' i) (fun j => (hK j j.2).1) (fun j => (hJ j j.2).2.1)
    (fun j => (hJ j j.2).1) (fun i => (hK' i _).1) (fun i => (hJ' i (Nat.le_of_lt_succ i.2)).2.1) (fun i => (hJ' i _).1)
    (fun j => (hK j j.2).2) (fun i => (hK' i _).2)
    (fun x y => P (ptX N e x y) (ext (P := fun j => GfC (V' j)) (N + 1) y)) ?_ ?_]
  · letI : ∀ j : Fin N, Fintype (FinCl (V j) (J j)) := fun j =>
      @Fintype.ofFinite _ (ClassFin.finite_finCl_and_gamOrd _ _ (hV j j.2) (hJ j j.2).2.1).1
    letI : ∀ j : Fin (N + 1), Fintype (FinCl (V' j) (J' j)) := fun j =>
      @Fintype.ofFinite _ (ClassFin.finite_finCl_and_gamOrd _ _ (hV' j (Nat.le_of_lt_succ j.2))
        (hJ' j (Nat.le_of_lt_succ j.2)).2.1).1
    have key := fun d (hd : d ∈ τ.support) => (one_term (hc d hd) hF hFa (hc' d hd) hF' hFa' h μ fd J
      (fun n hn => ⟨(hJ n hn).2.1, ⟨_, (hK n hn).1, (hJ n hn).1, (hK n hn).2⟩, fun k hk => (hJ n hn).2.2 k hk d hd⟩) μ' fd' J'
      (fun n hn => ⟨(hJ' n hn.le).2.1, ⟨_, (hK' n hn.le).1, (hJ' n hn.le).1, (hK' n hn.le).2⟩,
        fun k hk => (hJ' n hn.le).2.2.1 hn k hk d hd⟩)
      ⟨(hJ' N le_rfl).2.1, ⟨_, (hK' N le_rfl).1, (hJ' N le_rfl).1, (hK' N le_rfl).2⟩,
        fun k hk => (hJ' N le_rfl).2.2.2 rfl k hk d hd⟩)
    rw [Finsupp.sum, Finset.sum_congr rfl fun d hd => congrArg (τ d * ·) (key d hd)]
    simp only [finsum_eq_sum_of_fintype, hP, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_left_comm _ _ _
  · intro y j x
    refine ⟨fun γ hγ z => ?_, fun k hk z => ?_⟩
    · refine hrat (fun i _ => ?_) (fun i _ => ⟨1, one_mem _, (one_mul _).symm⟩) (pN _ _) (pN _ _)
      rw [pU, pU]
      exact up _ _ γ hγ z i
    · have := r1 (Function.update (β := fun j => GfC (V j)) (ptX N e x y) (j : ℕ) z) (ext (P := fun j => GfC (V' j)) (N + 1) y)
        j j.2 k hk
      rw [Function.update_self, Function.update_idem] at this
      simpa only [pU] using this
  · intro x i y
    refine ⟨fun γ hγ z => ?_, fun k hk z => ?_⟩
    · refine hrat (fun j hj => ⟨1, one_mem _, ?_⟩) (fun j _ => ?_) (pN _ _) (pN _ _)
      · rw [one_mul, ptX, ptX, Function.update_of_ne hj.ne, Function.update_of_ne hj.ne]
      · rw [ext_update (P := fun j => GfC (V' j)), ext_update (P := fun j => GfC (V' j))]
        exact up _ _ γ hγ z j
    · simp only [ptX, ext_update (P := fun j => GfC (V' j))]
      obtain ⟨i, hi⟩ := i
      rcases (Nat.le_of_lt_succ hi).eq_or_lt with rfl | hi'
      · have := r3 (Function.update (ext (P := fun j => GfC (V j)) i x) i (e z))
          (Function.update (ext (P := fun j => GfC (V' j)) (i + 1) y) i z) k (by simp) hk
        simpa only [Function.update_self, Function.update_idem] using this
      · have := r2 (Function.update (ext (P := fun j => GfC (V j)) N x) N (e (ext (P := fun j => GfC (V' j)) (N + 1) y N)))
          (Function.update (ext (P := fun j => GfC (V' j)) (N + 1) y) i z) i hi' k hk
        simpa only [Function.update_self, Function.update_idem, Function.update_of_ne hi'.ne'] using this

end Total

end GlobalTheory.JetsOne

end
