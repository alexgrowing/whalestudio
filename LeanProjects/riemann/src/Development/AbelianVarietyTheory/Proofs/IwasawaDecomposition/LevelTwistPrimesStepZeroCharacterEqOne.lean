import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.LevRead Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.GLev0

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre}

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)}

theorem loc_mem_U (S : StepLevel F E σ J T f bad) {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (hx : x ∈ UPts σ J (v.adicCompletion F)) : afsplitU v x 1 ∈ S.U ↔ x ∈ S.Uloc v := by
  rw [S.U_eq]
  refine ⟨fun h1 => afsplit_right1 v x 1 ▸ h1.2 v, fun h1 => ⟨afsplitU_mem v _ _ x 1 hx (one_mem _), fun v' => ?_⟩⟩
  by_cases e : v' = v
  · subst e
    rwa [afsplit_right1]
  · rw [bc_afsplitU_ne e]
    exact one_mem _

theorem loc_comm (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) {k : GL (Fin n) (AfE F E)} (hk : bc (prV (E := E) v) k = 1)
    (y : GL (Fin n) (AfE F E)) : y * afsplitU v x 1 * k = y * k * (afsplitU v x 1)⁻¹⁻¹ := by
  rw [inv_inv, mul_assoc, mul_assoc]
  refine congrArg _ (gl_ext fun v' => ?_)
  rw [map_mul, map_mul]
  by_cases e : v' = v
  · subst e
    rw [hk, mul_one, one_mul]
  · rw [bc_afsplitU_ne e, mul_one, one_mul]

theorem loc_inv_ne (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) {v' : HeightOneSpectrum (𝓞 F)} (e : v' ≠ v) :
    bc (prV (E := E) v') (afsplitU v x 1)⁻¹ = bc (prV (E := E) v') (1 : GL (Fin n) (AfE F E)) := by
  rw [map_inv, bc_afsplitU_ne e, inv_one, map_one]

theorem loc_int {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : ∀ y, y ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔ ∀ b, y b ∈ intV E v)
    {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hx : x ∈ levelVL σ J v L) :
    (∀ a b, (afsplitU v x 1).1 a b ∈ RInt F E) ∧ (∀ a b, ((afsplitU v x 1)⁻¹).1 a b ∈ RInt F E) ∧
      ∀ a b, ((afsplitU v x 1)⁻¹⁻¹).1 a b ∈ RInt F E := by
  have h1 : ∀ a b, (afsplitU v x 1).1 a b ∈ RInt F E := afsplitC_int v _ _ (entry_mem hL hx) (afsplit_one_mem _)
  refine ⟨h1, fun a b => ?_, by rwa [inv_inv]⟩
  rw [afsplitU_inv_coe, inv_one]
  exact afsplitC_int v _ _ (entry_mem hL (inv_mem hx)) (afsplit_one_mem _) a b

theorem bc_conj {k : GL (Fin n) (AfE F E)} (hk : bc (prV (E := E) v) k = 1) (z : GL (Fin n) (AfE F E)) :
    bc (prV (E := E) v) (k⁻¹ * z * k) = bc (prV (E := E) v) z := by
  rw [map_mul, map_mul, map_inv, hk, inv_one, one_mul, mul_one]

theorem valued_conj_le (S : StepLevel F E σ J T f bad) {w : HeightOneSpectrum (𝓞 E)} (hw : w.under (𝓞 F) = v)
    (hL : ∀ y, y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔ ∀ b, y b ∈ intV E v)
    {k z : GL (Fin n) (AfE F E)} (hk : bc (prV (E := E) v) k = 1) (hz : z ∈ S.U) (a b : Fin n) :
    Valued.v (adAt F w ((k⁻¹ * z * k).1 a b)) ≤ 1 := by
  rw [bc_adAt_congr hw (bc_conj hk z)]
  exact valued_adAt_le hw (entry_mem hL (S.Uloc_lev _ (((S.U_eq z).1 hz).2 _)) a b)

theorem exists_red_conj (S : StepLevel F E σ J T f bad) {w : HeightOneSpectrum (𝓞 E)} (hw : w.under (𝓞 F) = v)
    (hL : ∀ y, y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔ ∀ b, y b ∈ intV E v)
    {k x : GL (Fin n) (AfE F E)} (hk : bc (prV (E := E) v) k = 1) (hx : x ∈ S.U) :
    ∃ A : GL (Fin n) (𝓞 E ⧸ w.asIdeal), IsRed w (k⁻¹ * x⁻¹ * k) A.1 ∧ IsRed w x (A⁻¹).1 := by
  have einv : (k⁻¹ * x⁻¹ * k)⁻¹ = k⁻¹ * x * k := by group
  obtain ⟨A, hA⟩ := exists_isRed (P := w) (x := k⁻¹ * x⁻¹ * k) (valued_conj_le S hw hL hk (inv_mem hx))
    (by rw [einv]; exact valued_conj_le S hw hL hk hx)
  obtain ⟨A', hA'⟩ := exists_isRed (P := w) (x := k⁻¹ * x * k) (valued_conj_le S hw hL hk hx)
    (by rw [← einv, inv_inv]; exact valued_conj_le S hw hL hk (inv_mem hx))
  have h4 := hA'.mul hA
  rw [← einv, inv_mul_cancel] at h4
  have e1 : A' = A⁻¹ := eq_inv_of_mul_eq_one_left (Units.ext (h4.unique isRed_one))
  exact ⟨A, hA, e1 ▸ hA'.congr hw (bc_conj hk x)⟩

theorem red_inv {w : HeightOneSpectrum (𝓞 E)} {x : GL (Fin n) (AfE F E)} {A A' : GL (Fin n) (𝓞 E ⧸ w.asIdeal)}
    (h : IsRed w x⁻¹ A.1) (h' : IsRed w x A'.1) : A = A'⁻¹ := by
  have h1 := h'.mul h
  rw [mul_inv_cancel] at h1
  exact eq_inv_of_mul_eq_one_right (Units.ext (h1.unique isRed_one))

theorem conj_eq (y x k : GL (Fin n) (AfE F E)) : y * x * k = y * k * (k⁻¹ * x⁻¹ * k)⁻¹ := by group

theorem mat_one {gp : Fin 2 → ℕ} (G : GLoc F E σ gp) (i : Fin 2) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : G.mat i v h 1 x = x.1.map (G.phi i v h) := by
  unfold GLoc.mat
  rw [inv_one, one_mul, mul_one]
  rfl

theorem frame_one (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (hφ : ∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a)
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : ∀ y, y ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔ ∀ b, y b ∈ intV E v)
    (x : Fin n → v.adicCompletion F) :
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) L, ∀ b, φ (y b) = x b) ↔
      ∀ b, (((1 : GL (Fin n) (v.adicCompletion F))⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F := by
  rw [inv_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨?_, fun hx => ⟨fun b => (1 : E) ⊗ₜ[F] x b, (hL _).2 fun b => one_tmul_mem v (hx b), fun b => hφ _⟩⟩
  rintro ⟨z, hz, e⟩ b
  rw [← e b]
  exact phi_mem _ hφ ((hL z).1 hz b)

theorem redM_mat {gp : Fin 2 → ℕ} (G : GLoc F E σ gp) (i : Fin 2) (h : (gp i : 𝓞 F) ∈ v.asIdeal) {w : HeightOneSpectrum (𝓞 E)}
    (ρ : 𝓞 E ⧸ w.asIdeal →+* Formalism.L2.Forms.kv F v)
    (hres : ∀ (z : AfE F E) (c : 𝓞 E ⧸ w.asIdeal), HasRes w (adAt F w z) c →
        ∃ hh : G.phi i v h (prV (E := E) v z) ∈ v.adicCompletionIntegers F,
          IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hh⟩ = ρ c)
    {xa : GL (Fin n) (AfE F E)} {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.asIdeal)} (hA : IsRed w xa A) :
    redM F v (G.mat i v h 1 (bc (prV (E := E) v) xa)) = A.map ρ := by
  rw [mat_one]
  ext a b
  obtain ⟨hh, e⟩ := hres _ _ (hA a b)
  exact (dif_pos hh).trans e

end Generic

theorem vGs_inj {w w' : HeightOneSpectrum (𝓞 B.host.E)} (hw : w ∈ (B.primes X).vGs) (hw' : w' ∈ (B.primes X).vGs)
    (e : w'.under (𝓞 B.host.F) = w.under (𝓞 B.host.F)) : w' = w := by
  rcases (under_eq_iff B.host w w').1 e with h | h
  · exact h
  · have := (levOk_base B X).split w (by simpa using hw)
    rw [← h] at this
    exact absurd (by simpa using hw') this

theorem natCast_mem_iff {v : HeightOneSpectrum (𝓞 B.host.F)} {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (h1 : (a : 𝓞 B.host.F) ∈ v.asIdeal) (h2 : (b : 𝓞 B.host.F) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes ha hb).2 hab)).map (Int.castRingHom (𝓞 B.host.F))
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by simpa using h1)) (Ideal.mul_mem_left _ _ (by simpa using h2))

theorem T_notMem (X : PreX B.toPre) (u : B.Word) (i : Fin 2) {v : HeightOneSpectrum (𝓞 B.host.F)} (h : (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal) :
    (B.T u : 𝓞 B.host.F) ∉ v.asIdeal := fun hT =>
  natCast_mem_iff ((BasePrimes.primes_ok B X).1.T_prime u) ((BasePrimes.primes_ok B X).1.g_prime i)
    ((BasePrimes.primes_ok B X).1.T_ne_g u i) hT h

theorem under_ne_of_vT (u : B.Word) (i : Fin 2) {v : HeightOneSpectrum (𝓞 B.host.F)} (h : (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal)
    {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ (B.primes X).vT u) : P.under (𝓞 B.host.F) ≠ v := by
  rintro rfl
  have hPr := (BasePrimes.primes_ok B X).1
  have h1 : (B.primes X).piT u ∈ P.asIdeal := by
    have h0 : (B.primes X).piT u ≠ 0 := fun h0 => by
      have := hPr.piT_norm u
      rw [h0, zero_mul] at this
      exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
    exact (Formalism.L2.Col.mem_divs h0 P).1 hP
  have h2 : ((B.primes X).T u : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hPr.piT_norm u]; exact Ideal.mul_mem_right _ _ h1
  refine T_notMem X u i h ?_
  show (B.T u : 𝓞 B.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))
  rw [Ideal.mem_comap, map_natCast]
  exact h2

theorem exists_natCast {w : HeightOneSpectrum (𝓞 B.host.E)} (hw : w ∈ (B.primes X).vGs) (c : 𝓞 B.host.E ⧸ w.asIdeal) :
    ∃ n : ℕ, (n : 𝓞 B.host.E ⧸ w.asIdeal) = c := by
  classical
  have hPr := (BasePrimes.primes_ok B X).1
  obtain ⟨i, hi⟩ : ∃ i, w ∈ (B.primes X).vG i := by
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have hN := hPr.vG_norm i w hi
  have hp := hPr.g_prime i
  haveI : Fact (B.host.g i).Prime := ⟨hp⟩
  haveI := w.isMaximal
  letI : Field (𝓞 B.host.E ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Fintype (𝓞 B.host.E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (𝓞 B.host.E ⧸ w.asIdeal) = B.host.g i := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact hN
  haveI : CharP (𝓞 B.host.E ⧸ w.asIdeal) (B.host.g i) := charP_of_card_eq_prime hc
  obtain ⟨a, rfl⟩ := (ZMod.ringEquiv (𝓞 B.host.E ⧸ w.asIdeal) hc).surjective c
  exact ⟨a.val, by rw [ZMod.natCast_val]; rfl⟩

theorem sig_eq (x : 𝓞 B.host.E) : (B.sp.cm.sig : B.host.E →ₐ[B.host.F] B.host.E) (x : B.host.E) =
    ((B.fields.conjO x : 𝓞 B.host.E) : B.host.E) := by
  rw [B.fields_conjO_coe]
  exact B.fields_star (x : B.host.E)

theorem phi_one_tmul {σ : B.host.E →ₐ[B.host.F] B.host.E} (G : GLoc B.host.F B.host.E σ B.host.g) (i : Fin 2)
    (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal) (a : v.adicCompletion B.host.F) :
    G.phi i v h ((1 : B.host.E) ⊗ₜ[B.host.F] a) = a := by
  show (G.sp i v h _).1 = a
  rw [G.sp_alg]

theorem exists_w (G : GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (hG : G.piG = X.piG) (i : Fin 2)
    (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal) :
    ∃ w ∈ (B.primes X).vG i, ∃ ρ : 𝓞 B.host.E ⧸ w.asIdeal →+* Formalism.L2.Forms.kv B.host.F v, w.under (𝓞 B.host.F) = v ∧
      ∀ (z : AfE B.host.F B.host.E) (c : 𝓞 B.host.E ⧸ w.asIdeal), HasRes w (adAt B.host.F w z) c →
        ∃ hh : G.phi i v h (prV (E := B.host.E) v z) ∈ v.adicCompletionIntegers B.host.F,
          IsLocalRing.residue (v.adicCompletionIntegers B.host.F) ⟨_, hh⟩ = ρ c := by
  obtain ⟨w, ρ, hu, hw, hz⟩ := exists_prime (G.phi i v h) (phi_one_tmul G i v h)
  refine ⟨w, ?_, ρ, hu, hz⟩
  have hPr := (BasePrimes.primes_ok B X).1
  have h0 : B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun h0 => by
    have := hPr.piG_norm i
    rw [h0, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  refine (Formalism.L2.Col.mem_divs h0 w).2 ((hw _).2 ?_)
  have := G.sp_pi i v h
  rw [hG, sig_eq] at this
  exact this

variable (I : TC B X)

theorem notMem_twistPrimes_initialTuple (P : HeightOneSpectrum (𝓞 B.host.E)) : P ∉ QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) := by
  have h := I.twistPrimes_reference_tuple_eq_empty
  intro hP
  have : P ∈ I.Q I.mu0 := hP
  rw [h] at this
  exact absurd this (Finset.notMem_empty P)

theorem levelTypePrimes_stepZero_eq_colLev (hI : I.Ok) (u : B.Word) (b : (I.stp u I.mu0 0).β) :
    levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 b = colLev I.Ch 0 := by
  obtain ⟨b1, hb⟩ := Option.isSome_iff_exists.1 ((b.2).2 (by have := B.R.two_le_m; omega))
  unfold levGAt
  rw [hb]
  exact (hI.idx_ok I.mu0).zero_G b1

theorem coset0 {a : I.ι} {u : B.Word} (p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) : cosetIn p = fun _ => ∅ := by
  have h : p.1.2 = ∅ := by
    have := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by have := B.R.two_le_m; omega)] at this
    exact this
  funext P
  ext z
  simp [cosetIn, h]

theorem ufGL_eq_one {n : ℕ} {γ : UF B.host.E n} (h : ufGL B.host.E n γ = 1) : γ = 1 := by
  have h1 : (toGLm B.host.E n) γ.1 = (toGLm B.host.E n) 1 := by rw [map_one]; exact h
  exact Subtype.ext ((toGLm B.host.E n).injective h1)

theorem lev_iff (hI : I.Ok) {u : B.Word} {Lb : Unit → Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)}
    {U : Unit → Subgroup (GA B (B.R.N 0))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)}
    {st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E} {k : Unit → GA B (B.R.N 0)}
    (hR : I.Reads u I.mu0 0 (fun _ => ()) Lb U chi y st k) (c : (I.stp u I.mu0 0).Cl) {x m : GA B (B.R.N 0)}
    (hxm : y c * x * k () = y c * k () * m⁻¹) (hm : m ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N 0))
    (h1 : ∀ i j, (m : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) (AfE B.host.F B.host.E)) i j ∈ RInt B.host.F B.host.E)
    (h2 : ∀ i j, ((m⁻¹ : GA B (B.R.N 0)) : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) (AfE B.host.F B.host.E)) i j ∈
      RInt B.host.F B.host.E)
    (hT : ∀ P ∈ (B.primes X).vT u, ∀ i j, adAt B.host.F P ((m : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) (AfE B.host.F B.host.E)) i j) =
      adAt B.host.F P (((1 : GA B (B.R.N 0)) : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) (AfE B.host.F B.host.E)) i j))
    {h : GLG B.host.E (B.R.N 0) (B.primes X).vGs} (hh : ∀ w : (B.primes X).vGs, IsRed w.1 m (h w : Matrix _ _ _)) :
    x ∈ U () ↔ ∀ w, h w ∈ (colLev I.Ch 0 w).H := by
  have hQ := notMem_twistPrimes_initialTuple I
  set p0 := ((I.stp u I.mu0 0).rep c).1.1 with hp0def
  have hp0 : IsPtOf B.sp.cm (y c * k ()) p0 :=
    (hR.pt c).of_extTo (fun P hP => absurd hP (hQ P)) (Finset.disjoint_right.2 fun {P} hP => absurd hP (hQ P))
  have hq := isPtOf_mul hQ hp0 hm h1 h2 (fun P hP => hT P hP) hh 1
  rw [← hxm] at hq
  rw [hR.lev c x _ hq]
  constructor
  · rintro ⟨κ, hg, he, -⟩
    have hγ : κ.1 = 1 := ufGL_eq_one hg
    have e : ((1, κ.2.1.1, κ.2.2.1) : UF B.host.E (B.R.N 0) × GLG B.host.E (B.R.N 0) (B.primes X).vGs ×
        GLQ B.host.E (B.R.N 0) (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K))) • p0 =
        ((1, h, 1) : UF B.host.E (B.R.N 0) × GLG B.host.E (B.R.N 0) (B.primes X).vGs ×
        GLQ B.host.E (B.R.N 0) (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K))) • p0 := by
      rw [← he, ← hγ]
      rfl
    have e2 := eq_of_smul_eq p0 e
    have hmem : (κ.2.1 : GLG B.host.E (B.R.N 0) (B.primes X).vGs) ∈ (colLev I.Ch 0).grp := by
      have h3 := κ.2.1.2
      generalize (κ.2.1 : GLG B.host.E (B.R.N 0) (B.primes X).vGs) = g at h3
      rwa [levelTypePrimes_stepZero_eq_colLev I hI u c.1] at h3
    intro w
    rw [← e2]
    exact hmem w (Set.mem_univ _)
  · intro hmem
    have hmem' : h ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).grp := by
      rw [levelTypePrimes_stepZero_eq_colLev I hI u c.1]
      exact fun w _ => hmem w
    refine ⟨(1, ⟨h, hmem'⟩, 1), map_one (ufGL B.host.E (B.R.N 0)), rfl, ?_⟩
    rw [coset0, coset0]

theorem colLev_zero (w : (B.primes X).vGs) : colLev I.Ch 0 w =
    ⟨HX (𝓞 B.host.E ⧸ w.1.asIdeal) (B.R.N 0) B.R.k B.R.t 0,
      lamX (I.Ch.psi0 w) (extChi fun s => I.Ch.chi s w) (B.R.N 0) B.R.k B.R.m B.R.t 0⟩ :=
  if_pos (by have := B.R.two_le_m; omega)

theorem mem_colLev_zero {w : (B.primes X).vGs} {g : GL (Fin (B.R.N 0)) (𝓞 B.host.E ⧸ w.1.asIdeal)} :
    g ∈ (colLev I.Ch 0 w).H ↔ g ∈ uniUT (B.R.N 0) (𝓞 B.host.E ⧸ w.1.asIdeal) B.R.k [] := by
  rw [colLev_zero]
  rfl

theorem chr_colLev (Λ : LevFam B.host.E B.LL (B.R.N 0) (B.primes X).vGs) (hΛ : Λ = colLev I.Ch 0) (g : Λ.grp) :
    ((Λ.chr g : B.LLˣ) : B.LL) = ∏ w : (B.primes X).vGs,
      I.Ch.psi0 w (supSum B.R.k (SX B.R.k B.R.m 0) ((g.1 w : GL _ _) : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) _)) := by
  have hΛ' : Λ = fun w => ⟨HX (𝓞 B.host.E ⧸ w.1.asIdeal) (B.R.N 0) B.R.k B.R.t 0,
      lamX (I.Ch.psi0 w) (extChi fun s => I.Ch.chi s w) (B.R.N 0) B.R.k B.R.m B.R.t 0⟩ :=
    hΛ.trans (funext (colLev_zero I))
  subst hΛ'
  rw [LevFam.chr, piChar]
  erw [MonoidHom.finset_prod_apply]
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  erw [MonoidHom.comp_apply]
  show ((lamGen _ _ _ _ _ _ _ : B.LLˣ) : B.LL) = _
  rw [lamGen, MonoidHom.mul_apply, Units.val_mul, supChar_val, MonoidHom.comp_apply, detChar_apply]
  simp
  rfl

theorem levelTwistPrimes_stepZero_character_eq_one (hI : I.Ok) (u : B.Word) (b : (I.stp u I.mu0 0).β)
    (g : (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 b).grp) :
    (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 b).chr g = 1 := by
  haveI : IsEmpty (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) := ⟨fun P => notMem_twistPrimes_initialTuple I P.1 P.2⟩
  rw [LevQFam.chr, piChar, Finset.univ_eq_empty, Finset.prod_empty]
  rfl

theorem chi_eq (hI : I.Ok) {u : B.Word} {Lb : Unit → Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)}
    {U : Unit → Subgroup (GA B (B.R.N 0))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)}
    {st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E} {k : Unit → GA B (B.R.N 0)}
    (hR : I.Reads u I.mu0 0 (fun _ => ()) Lb U chi y st k) (c : (I.stp u I.mu0 0).Cl) {x m : GA B (B.R.N 0)}
    (hx : x ∈ U ()) (hxm : y c * x * k () = y c * k () * m⁻¹) (hu : y c * x * k () ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N 0))
    {A : ∀ w : (B.primes X).vGs, Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) (𝓞 B.host.E ⧸ w.1.asIdeal)}
    (hA : ∀ w : (B.primes X).vGs, IsRed w.1 m (A w)) :
    ∃ h : GLG B.host.E (B.R.N 0) (B.primes X).vGs, (∀ w, h w ∈ (colLev I.Ch 0 w).H) ∧ (∀ w, (h w : Matrix _ _ _) = A w) ∧
      ((chi () ⟨x, hx⟩ : ℂˣ) : ℂ) = B.embLL (∏ w : (B.primes X).vGs,
        I.Ch.psi0 w (supSum B.R.k (SX B.R.k B.R.m 0) ((h w : GL _ _) : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) _))) := by
  have hQ := notMem_twistPrimes_initialTuple I
  haveI : NeZero (B.R.N 0) := ⟨by have := B.R.m_add_three_le_k; simp [Ranks.N]; omega⟩
  set p0 := ((I.stp u I.mu0 0).rep c).1.1 with hp0def
  have hp0 : IsPtOf B.sp.cm (y c * k ()) p0 :=
    (hR.pt c).of_extTo (fun P hP => absurd hP (hQ P)) (Finset.disjoint_right.2 fun {P} hP => absurd hP (hQ P))
  obtain ⟨q, hq⟩ := exists_pt (ST := (B.primes X).vT u) (SG := (B.primes X).vGs) hQ hu
  obtain ⟨κ, hg, he, -⟩ := (hR.lev c x q hq).1 hx
  have hγ : κ.1 = 1 := ufGL_eq_one hg
  have hq' : IsPtOf B.sp.cm (y c * x * k ()) (((I.stp u I.mu0 0).act c.1 κ ((I.stp u I.mu0 0).rep c)).1.1) := by
    rw [he]; exact hq
  have hchr := hR.chr c ⟨x, hx⟩ κ hg hq'
  have e : ((I.stp u I.mu0 0).act c.1 κ ((I.stp u I.mu0 0).rep c)).1.1 =
      ((1, κ.2.1.1, κ.2.2.1) : UF B.host.E (B.R.N 0) × GLG B.host.E (B.R.N 0) (B.primes X).vGs ×
        GLQ B.host.E (B.R.N 0) (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K))) • p0 := by
    rw [← hγ]
    rfl
  rw [e, hxm] at hq'
  have hmem : (κ.2.1 : GLG B.host.E (B.R.N 0) (B.primes X).vGs) ∈ (colLev I.Ch 0).grp := by
    have h3 := κ.2.1.2
    generalize (κ.2.1 : GLG B.host.E (B.R.N 0) (B.primes X).vGs) = g at h3
    rwa [levelTypePrimes_stepZero_eq_colLev I hI u c.1] at h3
  refine ⟨κ.2.1, fun w => hmem w (Set.mem_univ _), fun w => (eq_red hp0 hq' w (hA w)).symm, ?_⟩
  rw [hchr]
  congr 1
  show (((levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr κ.2.1 *
    (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr κ.2.2 : B.LLˣ) : B.LL) = _
  rw [levelTwistPrimes_stepZero_character_eq_one I hI u c.1, mul_one, chr_colLev I _ (levelTypePrimes_stepZero_eq_colLev I hI u c.1)]

theorem latS_iff {u : B.Word} {L : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)}
    (hL : ∀ x, x ∈ L ↔ x ∈ baseL B (B.R.N 0) (X.piT u)) {i : Fin 2} {v : HeightOneSpectrum (𝓞 B.host.F)}
    (h : (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal) (y : Fin (B.R.N 0) → B.host.E ⊗[B.host.F] v.adicCompletion B.host.F) :
    y ∈ latS (F := B.host.F) (v.adicCompletion B.host.F) (intV B.host.E v) L ↔ ∀ b, y b ∈ intV B.host.E v := by
  classical
  refine mem_latS_iff (T_notMem X u i h) (fun x hx j => ?_) (fun j => (hL _).2 fun b => ?_) y
  · obtain ⟨r, hr, -⟩ := (hL x).1 hx j
    exact ⟨r, hr⟩
  · have hPr := (BasePrimes.primes_ok B X).1
    refine ⟨if b = j then (B.T u : 𝓞 B.host.E) else 0, ?_, fun _ => ?_⟩
    · rw [Pi.single_apply]
      split_ifs <;> simp
    · split_ifs
      · refine ⟨B.fields.conjO ((B.primes X).piT u), ?_⟩
        rw [hPr.piT_norm u]
      · exact dvd_zero _

theorem inJ_iff {κ L : Type} [Field κ] [Field L] (ρ : κ →+* L) (hn : B.R.N 0 = B.R.k)
    (A : GL (Fin (B.R.N 0)) κ) :
    InJ B.R.k B.R.t (B.R.N 0) false (A.1.map ρ) ↔ A ∈ uniUT (B.R.N 0) κ B.R.k [] := by
  have hlt : ∀ x : Fin (B.R.N 0), (x : ℕ) < B.R.k := fun x => hn ▸ x.2
  have hb : ∀ x : Fin (B.R.N 0), Formalism.L2.Forms.blkOf B.R.k B.R.t x = x := fun x => if_pos (hlt x)
  have hf : ∀ x : Fin (B.R.N 0), fine B.R.k [] x = x := fun x => if_pos (hlt x)
  simp only [InJ, hb, Matrix.map_apply]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    refine ⟨fun i j hij => ?_, fun i hi => ?_⟩
    · have hij' : (j : ℕ) < i := by simpa [hf] using hij
      exact ρ.injective ((h1 i j hij').trans (map_zero ρ).symm)
    · exact ρ.injective ((h2 i hi).trans (map_one ρ).symm)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i hi => ?_, fun i j hj => absurd hj (by have := j.2; omega), fun h => absurd h (by simp)⟩
    · rw [h1 (show fine B.R.k [] j < fine B.R.k [] i by simpa [hf] using hij), map_zero]
    · rw [h2 i hi, map_one]

theorem mem_vGs {w : HeightOneSpectrum (𝓞 B.host.E)} : w ∈ (B.primes X).vGs ↔ ∃ i, w ∈ (B.primes X).vG i := by
  classical
  unfold Primes.vGs
  simp only [Finset.mem_union, Fin.exists_fin_two]

theorem g_mem {i : Fin 2} {w : HeightOneSpectrum (𝓞 B.host.E)} (hw : w ∈ (B.primes X).vG i) :
    (B.host.g i : 𝓞 B.host.E) ∈ w.asIdeal := by
  have hPr := (BasePrimes.primes_ok B X).1
  have h0 : B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun h0 => by
    have := hPr.piG_norm i
    rw [h0, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have h1 := Ideal.mul_mem_left _ ((B.primes X).piG i) ((Formalism.L2.Col.mem_divs h0 w).1 hw)
  rwa [hPr.piG_norm i] at h1

theorem g_mem_under {i : Fin 2} {w : HeightOneSpectrum (𝓞 B.host.E)} (hw : w ∈ (B.primes X).vG i) :
    (B.host.g i : 𝓞 B.host.F) ∈ (w.under (𝓞 B.host.F)).asIdeal := by
  show (B.host.g i : 𝓞 B.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))
  rw [Ideal.mem_comap, map_natCast]
  exact g_mem hw

theorem prod_places (Φ : (B.primes X).vGs → ℂ)
    (f : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 B.host.F)), (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal → ℂ)
    (hf : ∀ i v h, ∃ (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ (B.primes X).vG i), w.under (𝓞 B.host.F) = v ∧
      f i v h = Φ ⟨w, mem_vGs.2 ⟨i, hw⟩⟩) :
    ∏ w, Φ w = ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal), f i v h := by
  classical
  have hPr := (BasePrimes.primes_ok B X).1
  let Ψ : HeightOneSpectrum (𝓞 B.host.E) → ℂ := fun w => if h : w ∈ (B.primes X).vGs then Φ ⟨w, h⟩ else 1
  have h1 : ∀ i, (∏ᶠ (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal), f i v h) =
      ∏ w ∈ (B.primes X).vG i, Ψ w := fun i => by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := ((B.primes X).vG i).image fun w => w.under (𝓞 B.host.F)) ?_,
      Finset.prod_image fun w hw w' hw' e => vGs_inj (X := X) (mem_vGs.2 ⟨i, hw'⟩) (mem_vGs.2 ⟨i, hw⟩) e]
    · refine Finset.prod_congr rfl fun w hw => ?_
      obtain ⟨w', hw', e, e'⟩ := hf i _ (g_mem_under hw)
      obtain rfl : w' = w := vGs_inj (X := X) (mem_vGs.2 ⟨i, hw⟩) (mem_vGs.2 ⟨i, hw'⟩) e
      rw [finprod_eq_dif, dif_pos (g_mem_under hw), e']
      simp only [Ψ]
      rw [dif_pos (mem_vGs.2 ⟨i, hw⟩)]
    · intro v hv
      rw [Function.mem_mulSupport, finprod_eq_dif] at hv
      split_ifs at hv with h
      · obtain ⟨w, hw, e, -⟩ := hf i v h
        exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨w, hw, e⟩)
      · exact absurd rfl hv
  have hd : Disjoint ((B.primes X).vG 0) ((B.primes X).vG 1) := Finset.disjoint_left.2 fun w h0 h1 =>
    natCast_mem_iff (hPr.g_prime 0) (hPr.g_prime 1) hPr.g_ne (g_mem_under h0) (g_mem_under h1)
  rw [Fin.prod_univ_two, h1, h1, ← Finset.prod_union hd]
  have e : (B.primes X).vG 0 ∪ (B.primes X).vG 1 = (B.primes X).vGs := by
    ext w
    rw [mem_vGs, Finset.mem_union, Fin.exists_fin_two]
  rw [e, ← Finset.prod_coe_sort (B.primes X).vGs Ψ]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp only [Ψ]
  rw [dif_pos w.2]

theorem norm_additiveCharacter_typePrime_eq_one (w : (B.primes X).vGs) (a : 𝓞 B.host.E ⧸ w.1.asIdeal) : ‖B.embLL (I.Ch.psi0 w a)‖ = 1 := by
  obtain ⟨i, hi⟩ := mem_vGs.1 w.2
  have h0 : ((B.host.g i : ℕ) : 𝓞 B.host.E ⧸ w.1.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.1.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact g_mem hi
  refine Complex.norm_eq_one_of_pow_eq_one (n := B.host.g i) ?_ ((BasePrimes.primes_ok B X).1.g_prime i).ne_zero
  rw [← map_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, h0, zero_mul, AddChar.map_zero_eq_one, map_one]

theorem supSum_inv {κ : Type} [CommRing κ] {n a : ℕ} (S : Finset ℕ) {g : GL (Fin n) κ} (hg : g ∈ uniUT n κ a []) :
    supSum a S (g⁻¹).1 = -supSum a S g.1 :=
  congrArg Multiplicative.toAdd (map_inv (supHom n κ a [] S) ⟨g, hg⟩)

theorem lamJ_zero {κ L : Type} [CommRing κ] [Field L] (ρ : κ →+* L) (ψ : AddChar L ℂ) (χ : ℕ → MulChar L ℂ) {n : ℕ} (k m t : ℕ)
    (A : Matrix (Fin n) (Fin n) κ) : Formalism.L2.Forms.lamJ ψ χ k t 0 k (A.map ρ) = ψ (ρ (supSum k (SX k m 0) A)) := by
  rw [Formalism.L2.Forms.lamJ, Finset.range_zero, Finset.prod_empty, mul_one, supSum, map_sum ρ]
  refine congrArg ψ (Finset.sum_congr rfl fun x _ => ?_)
  rw [map_sum ρ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [apply_ite ρ, map_zero]
  refine if_congr (and_congr_right fun h1 => and_congr_right fun h2 => ?_) rfl rfl
  simp only [SX, Finset.mem_filter, Finset.mem_range]
  omega

section Level

variable {u : B.Word} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
  (S : StepLevel B.host.F B.host.E B.sp.cm.sig (1 : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.host.E) T f bad)
  {y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)}
  {st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E} {k : Unit → GA B (B.R.N 0)}
  (hR : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => S.Lb) (fun _ => S.U) (fun _ => S.chi) y st k)
  (G : GLoc B.host.F B.host.E B.sp.cm.sig B.host.g)

include hR in
theorem k_triv {i : Fin 2} {v : HeightOneSpectrum (𝓞 B.host.F)} (h : (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal) :
    bc (prV (E := B.host.E) v) (k ()) = 1 :=
  hR.k_off () v (T_notMem X u i h) (fun ⟨P, hP, _⟩ => notMem_twistPrimes_initialTuple I P hP) (Or.inl rfl)

include hR in

theorem mem_Uloc (hI : I.Ok) (hG : G.piG = X.piG) (i : Fin 2) (v : HeightOneSpectrum (𝓞 B.host.F))
    (h : (B.host.g i : 𝓞 B.host.F) ∈ v.asIdeal) (x : GL (Fin (B.R.N 0)) (B.host.E ⊗[B.host.F] v.adicCompletion B.host.F))
    (hx : x ∈ levelVL B.sp.cm.sig (1 : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.host.E) v S.Lb) :
    x ∈ S.Uloc v ↔ InJ B.R.k B.R.t (B.R.N 0) false (redM B.host.F v (G.mat i v h 1 x)) := by
  obtain ⟨w, hw, ρ, hu, hres⟩ := exists_w G hG i v h
  have hw' : w ∈ (B.primes X).vGs := mem_vGs.2 ⟨i, hw⟩
  obtain ⟨c, -⟩ := hR.onto ()
  have hL := latS_iff (hR.lb ()) h
  obtain ⟨i1, i2, i3⟩ := loc_int hL hx
  choose A hA using fun w' : (B.primes X).vGs => exists_isRed (P := w'.1) (x := (afsplitU v x 1)⁻¹)
    (fun a b => (mem_rInt_iff _ _ _).1 (i2 a b) _) (fun a b => (mem_rInt_iff _ _ _).1 (i3 a b) _)
  have key := lev_iff I hI hR c (loc_comm x (k_triv I S hR h) (y c)) (inv_mem (afsplitU_mem v _ _ x 1 hx.1 (one_mem _))) i2 i3
    (fun P hP => bc_adAt_congr rfl (loc_inv_ne x (under_ne_of_vT u i h hP))) hA
  obtain ⟨A', hA'⟩ := exists_isRed (P := w) (x := afsplitU v x 1) (fun a b => (mem_rInt_iff _ _ _).1 (i1 a b) _)
    (fun a b => (mem_rInt_iff _ _ _).1 (i2 a b) _)
  have e1 : A ⟨w, hw'⟩ = A'⁻¹ := red_inv (hA ⟨w, hw'⟩) hA'
  have e0 : redM B.host.F v (G.mat i v h 1 x) = A'.1.map ρ :=
    (congrArg (fun z => redM B.host.F v (G.mat i v h 1 z)) (afsplit_right1 v x 1)).symm.trans (redM_mat G i h ρ hres hA')
  rw [e0]
  refine (loc_mem_U S hx.1).symm.trans ?_
  refine key.trans (Iff.trans ?_ (inJ_iff ρ (by simp [Ranks.N]) A').symm)
  refine ⟨fun h1 => ?_, fun h1 w' => (mem_colLev_zero I).2 ?_⟩
  · have := (mem_colLev_zero I).1 (h1 ⟨w, hw'⟩)
    rwa [e1, inv_mem_iff] at this
  · by_cases e : w' = ⟨w, hw'⟩
    · subst e
      rwa [e1, inv_mem_iff]
    · have e2 : w'.1.under (𝓞 B.host.F) ≠ v := fun e3 => e (Subtype.ext (vGs_inj (X := X) hw' w'.2 (e3.trans hu.symm)))
      have e3 : A w' = 1 := Units.ext ((hA w').unique (isRed_one.congr rfl (loc_inv_ne x e2).symm))
      rw [e3]
      exact one_mem _

set_option maxHeartbeats 800000 in
include hR in

theorem chi_prod (hI : I.Ok) (x : S.U) : ∃ h : GLG B.host.E (B.R.N 0) (B.primes X).vGs,
    (∀ w, h w ∈ uniUT (B.R.N 0) (𝓞 B.host.E ⧸ w.1.asIdeal) B.R.k []) ∧ (∀ w : (B.primes X).vGs, IsRed w.1 x.1 ((h w)⁻¹).1) ∧
      ((S.chi x : ℂˣ) : ℂ) = ∏ w : (B.primes X).vGs, B.embLL (I.Ch.psi0 w (supSum B.R.k (SX B.R.k B.R.m 0) (h w).1)) := by
  obtain ⟨c, -⟩ := hR.onto ()
  obtain ⟨p, hp, -⟩ := hR.k_std ()
  have hex : ∀ w : (B.primes X).vGs, ∃ A : GL (Fin (B.R.N 0)) (𝓞 B.host.E ⧸ w.1.asIdeal),
      IsRed w.1 ((k ())⁻¹ * x.1⁻¹ * k ()) A.1 ∧ IsRed w.1 x.1 (A⁻¹).1 := fun w => by
    obtain ⟨i, hi⟩ := mem_vGs.1 w.2
    exact exists_red_conj S rfl (latS_iff (hR.lb ()) (g_mem_under hi)) (k_triv I S hR (g_mem_under hi)) x.2
  choose A hA hA' using hex
  have hy : y c ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N 0) :=
    (mul_inv_cancel_right (y c) (k ())) ▸ mul_mem (hR.pt c).uni (inv_mem hp.uni)
  obtain ⟨h, h1, h2, h3⟩ := chi_eq I hI hR c x.2 (conj_eq (y c) x.1 (k ()))
    (mul_mem (mul_mem hy ((S.U_eq _).1 x.2).1) hp.uni) hA
  refine ⟨h, fun w => (mem_colLev_zero I).1 (h1 w), fun w => ?_, h3.trans (map_prod _ _ _)⟩
  have e : h w = A w := Units.ext (h2 w)
  exact e ▸ hA' w

set_option maxHeartbeats 800000 in
include hR in
theorem exists_glev (hI : I.Ok) (hG : G.piG = X.piG)
    (hψ : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ n : ℕ,
      G.psi0 j v h (n : kv B.host.F v) = B.embLL (I.Ch.psi0 w (n : 𝓞 B.fields.E ⧸ w.1.asIdeal))) :
    ∃ V : GLev S G B.R.k B.R.t 0 B.R.k (B.R.N 0) false, ∀ j v h, V.fr j v h = 1 := by
  refine ⟨⟨fun _ _ _ => 1, fun i v h x => ?_, fun i v h => mem_Uloc I S hR G hI hG i v h, fun x => ?_, fun x => ?_⟩,
    fun _ _ _ => rfl⟩
  · exact frame_one _ (phi_one_tmul G i v h) (latS_iff (hR.lb ()) h) x
  · obtain ⟨h, h1, h2, h3⟩ := chi_prod I S hR hI x
    rw [h3]
    refine prod_places _ _ fun i v hv => ?_
    obtain ⟨w, hw, ρ, hu, hres⟩ := exists_w G hG i v hv
    refine ⟨w, hw, hu, ?_⟩
    have hw' : w ∈ (B.primes X).vGs := mem_vGs.2 ⟨i, hw⟩
    rw [redM_mat G i hv ρ hres (h2 ⟨w, hw'⟩), lamJ_zero ρ _ _ B.R.k B.R.m B.R.t]
    obtain ⟨n, hn⟩ := exists_natCast hw' (supSum B.R.k (SX B.R.k B.R.m 0) ((h ⟨w, hw'⟩)⁻¹).1)
    rw [← hn, map_natCast ρ, hψ i v hv ⟨w, hw'⟩ hu n, hn, supSum_inv _ (h1 ⟨w, hw'⟩), AddChar.map_neg_eq_inv, map_inv₀, inv_inv]
  · obtain ⟨h, -, -, h3⟩ := chi_prod I S hR hI x
    rw [h3, norm_prod]
    exact Finset.prod_eq_one fun w _ => norm_additiveCharacter_typePrime_eq_one I w _

end Level

theorem exists_glev' (hI : I.Ok) {u : B.Word} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    {J : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.host.E} (hJ : J = 1) (S : StepLevel B.host.F B.host.E B.sp.cm.sig J T f bad)
    {y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)}
    {st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E} {k : Unit → GA B (B.R.N 0)}
    (hR : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => S.Lb) (fun _ => S.U) (fun _ => S.chi) y st k)
    (G : GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (hG : G.piG = X.piG)
    (hψ : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ n : ℕ,
      G.psi0 j v h (n : kv B.host.F v) = B.embLL (I.Ch.psi0 w (n : 𝓞 B.fields.E ⧸ w.1.asIdeal))) :
    ∃ V : GLev S G B.R.k B.R.t 0 B.R.k (B.R.N 0) false, ∀ j v h, V.fr j v h = 1 := by
  subst hJ
  exact exists_glev I S hR G hI hG hψ

theorem glev_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) (K : ClsTied (D := (I.rec7 l Z)) u 0 (Nat.zero_le _)), I.IdG l Z G → (∃ k, I.Reads u I.mu0 0 (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k) → ∃ V : GLev K.lev G B.R.k B.R.t 0 B.R.k (B.R.N 0) false, ∀ j v h, V.fr j v h = 1 := by
  intro B X I hI hP l Z u G K hG ⟨k, hR⟩
  exact exists_glev' I hI ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1 K.lev hR G hG.piG hG.psi

end GlobalTheory.Mem.Col2.TC.GLev0
