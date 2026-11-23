import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SelfDualPI
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.OneAddPowOfSq
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.LevZero
open scoped TensorProduct

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reL_rfl {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x; simp [reL, reV]

theorem reGL_rfl' {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  apply Units.ext; ext x y; rfl

theorem reGL_rfl_hom {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_rfl' R g

theorem exists_reindex {a b : ℕ} (h : a = b) {σ : E →ₐ[F] E} (J : Matrix (Fin a) (Fin a) E)
    {J' : Matrix (Fin b) (Fin b) E} (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ} {G : GLoc F E σ gp} {a' t nb skip fc : ℕ} {zl : Bool}
    (S' : Formalism.L2.Forms.StepLevel F E σ J' T f bad) (L' : GLev S' G a' t nb skip fc zl)
    {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin a → E))
    (y' : cl → UPts σ J' (FiniteAdeleRing (𝓞 F) F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y' c) : Cls S')))
    (y_lat : ∀ c (x : Fin b → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (reL h (lat c)) ↔
      ((y' c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S'.Lb)
    (st' : ∀ c, stab c →* UJ (σ : E →+* E) J') (st_inj : ∀ c, Function.Injective (st' c))
    (st_range : ∀ c (γ : UJ (σ : E →+* E) J'), γ ∈ (st' c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S'.U.map (MulAut.conj (y' c).1).toMonoidHom) :
    ∃ (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (L : GLev S G a' t nb skip fc zl)
      (y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (st : ∀ c, stab c →* UJ (σ : E →+* E) J),
      Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S)) ∧
      (∀ c (x : Fin a → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
        x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
        ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb) ∧
      (∀ c, Function.Injective (st c)) ∧
      (∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (st c).range ↔
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S.U.map (MulAut.conj (y c).1).toMonoidHom) ∧
      SameCar h S.Lb S'.Lb S.Uloc S'.Uloc S.U S'.U (fun c => (y c).1) (fun c => (y' c).1)
        (fun c s => (st c s).1) (fun c s => (st' c s).1) ∧
      ∀ i v hv, L'.fr i v hv = reGL h _ (L.fr i v hv) := by
  subst h
  obtain rfl : J' = J := by ext x y; exact hJ x y
  simp only [reL_rfl] at y_lat
  refine ⟨S', L', y', st', y_bij, y_lat, st_inj, st_range, ⟨(reL_rfl _).symm, fun v => ?_, ?_,
    fun c => (reGL_rfl' _ _).symm, fun c s => (reGL_rfl' _ _).symm⟩, fun i v hv => (reGL_rfl' _ _).symm⟩
  · rw [reGL_rfl_hom, Subgroup.map_id]
  · rw [reGL_rfl_hom, Subgroup.map_id]

end Gen

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem not_both_mem {p q : ℕ} (h : Nat.Coprime p q) (v : HeightOneSpectrum (𝓞 F)) (hp : (p : 𝓞 F) ∈ v.asIdeal)
    (hq : (q : 𝓞 F) ∈ v.asIdeal) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 F) (q : 𝓞 F) := Nat.Coprime.cast h
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hq)))

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ v.asIdeal := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ |>.isMaximal (by simpa using hpZ.ne_zero)
  obtain ⟨Q, hQ, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) (Ideal.span {(p : ℤ)})
  have hmem : (p : 𝓞 F) ∈ Q := by
    have : (p : ℤ) ∈ Q.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : (p : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

theorem inJ_iff {k : Type} [Field k] {n a t fc : ℕ} (ha : n ≤ a) (hfc : n ≤ fc) (M : Matrix (Fin n) (Fin n) k) :
    InJ a t fc false M ↔ ∀ i j : Fin n, (j < i → M i j = 0) ∧ M i i = 1 := by
  have hb : ∀ x : Fin n, blkOf a t x = x := fun x => if_pos (lt_of_lt_of_le x.2 ha)
  constructor
  · rintro ⟨h1, h2, -, -⟩ i j
    exact ⟨fun h => h1 i j (by rw [hb, hb]; exact h), h2 i (lt_of_lt_of_le i.2 ha)⟩
  · intro h
    refine ⟨fun x y hxy => (h x y).1 (by rw [hb, hb] at hxy; exact hxy), fun x _ => (h x x).2,
      fun x y hy => absurd y.2 (by omega), fun hz => absurd hz (by simp)⟩

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

set_option maxHeartbeats 1000000 in

theorem mem_Uloc_iff_iwU (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) {G : GLoc F E σ gp} {a t nb skip fc : ℕ}
    (L : GLev S G a t nb skip fc false) (ha : n ≤ a) (hfc : n ≤ fc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (hT : (T : 𝓞 F) ∉ v.asIdeal) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ UPts σ J (v.adicCompletion F)) :
    x ∈ S.Uloc v ↔ (L.fr i v hv)⁻¹ * bc ((RingHom.fst _ _).comp (G.sp i v hv).toRingHom) x * L.fr i v hv ∈ iwU F n v := by
  have hst : Formalism.L2.G.SplitStabL σ J v (G.sp i v hv) S.Lb (L.fr i v hv) :=
    Formalism.L2.G.splitStabL_of σ J v (G.sp i v hv) S.Lb (L.fr i v hv) (G.sp_sig i v hv)
      (Formalism.L2.G.split_integral_completion F E v _ (G.sp_alg i v hv))
      (Formalism.L2.G.self_dual_lattice_at F E n σ J v S.Lb T S.Lb_fin (fun x hx y hy => S.Lb_int y hy x hx)
        (fun y hy => S.Lb_dual y hy) hT) (L.fr_lat i v hv)
  have h1 := hst x hx
  rw [Formalism.L2.G.toFr_apply] at h1
  have key : ∀ g : GL (Fin n) (v.adicCompletionIntegers F),
      bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g =
        (L.fr i v hv)⁻¹ * bc ((RingHom.fst _ _).comp (G.sp i v hv).toRingHom) x * L.fr i v hv →
      (InJ a t fc false (redM F v (G.mat i v hv (L.fr i v hv) x)) ↔
        redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) g ∈ upperUni n _) := by
    intro g hg
    have e : G.mat i v hv (L.fr i v hv) x =
        (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g : GL (Fin n) (v.adicCompletion F)).1 := by
      rw [hg]; rfl
    rw [e, Formalism.L2.G.redM_bc]
    exact inJ_iff (k := Formalism.L2.Forms.kv F v) ha hfc _
  constructor
  · intro hU
    have hlev := S.Uloc_lev v hU
    obtain ⟨g, hg⟩ := h1.1 hlev
    exact Subgroup.mem_map.2 ⟨g, Subgroup.subset_closure ((key g hg).1 ((L.mem i v hv x hlev).1 hU)), hg⟩
  · intro hI
    obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 hI
    exact (L.mem i v hv x (h1.2 ⟨g, e⟩)).2
      ((key g e).2 (Formalism.L2.G.Triv.closure_upperUni _ _ (Subgroup.mem_comap.1 hg)))

set_option maxHeartbeats 1000000 in

theorem stab_class_lattice (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (M : Submodule (𝓞 E) (Fin n → E))
    (hfin : Module.Finite (𝓞 E) M) (hspan : Submodule.span E (M : Set (Fin n → E)) = ⊤)
    (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
        x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) M ↔
        (y⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (γ : GL (Fin n) E)
    (hγ : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ S.U.map (MulAut.conj y).toMonoidHom) (x : Fin n → E) :
    x ∈ M ↔ γ.1 *ᵥ x ∈ M := by
  obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 hγ
  have hk' := (S.U_eq k).1 hk
  have hst := ((GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin k).2
    ⟨hk'.1, fun v => S.Uloc_lev v (hk'.2 v)⟩).2
  have hM : ∀ z : Fin n → E, z ∈ M ↔ (y⁻¹).1 *ᵥ (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb := by
    intro z
    rw [← hy]
    have h1 : z ∈ Formalism.UG.CS.globLat (F := F) 1 M ↔
        ((1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))⁻¹).1 *ᵥ
          (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) M := Iff.rfl
    rwa [Formalism.UG.P.global_lattice_one_holds F E (Fin n) M hfin hspan, inv_one, Units.val_one, one_mulVec] at h1
  have e2 : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ.1 *ᵥ x) i)) =
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ).1 *ᵥ
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) := by
    funext b
    exact RingHom.map_mulVec (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 x b
  have e3 : y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ = k * y⁻¹ := by
    rw [← e]
    show y⁻¹ * (y * k * y⁻¹) = _
    group
  rw [hM, hM, e2, mulVec_mulVec, ← Units.val_mul, e3, Units.val_mul, ← mulVec_mulVec]
  exact hst _

end Loc

theorem clsCrd_zero (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    clsCrd D u 0 (Nat.zero_le _) c = reL (rank_eq_first_level D.R) (D.sp.crdLat0 (D.clsLat u 0 c)) := by
  unfold clsCrd reL Spaces.crdLat0
  rw [← Submodule.map_comp]
  rfl

theorem crdLat0_fin (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    Module.Finite (𝓞 D.host.E) (D.sp.crdLat0 (D.clsLat u 0 c)) :=
  Module.Finite.iff_fg.2 ((D.clsLat_lat u 0 c).fg.map _)

theorem crdLat0_span (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    Submodule.span D.host.E (D.sp.crdLat0 (D.clsLat u 0 c) : Set (Fin D.R.k → D.host.E)) = ⊤ := by
  have : (D.sp.crdLat0 (D.clsLat u 0 c) : Set (Fin D.R.k → D.host.E)) =
      (D.sp.crd0 : (D.sp.X 0).V →ₗ[D.host.E] (Fin D.R.k → D.host.E)) '' (D.clsLat u 0 c : Set (D.sp.X 0).V) := rfl
  rw [this, Submodule.span_image, (D.clsLat_lat u 0 c).span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact D.sp.crd0.surjective

set_option maxHeartbeats 4000000 in

theorem exists_colLevel (D : D7) (u : D.what₂.Word) {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (F : FormsTiedSym D u Ch chOf) :
    ∃ L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u),
      SameCar (rank_eq_first_level D.R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
        L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
        L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
        (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
        (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) ∧
      F.gl.sp = L.splitG ∧ ∀ i v h, F.glev0.fr i v h = reGL (rank_eq_first_level D.R) _ (L.frG i v h) := by
  obtain ⟨S, L, y, st, hbij, hlat, hinj, hrange, hcar, hfr⟩ :=
    exists_reindex (rank_eq_first_level D.R) (σ := sigD D) D.sp.gram0 (J' := gramN D 0 (Nat.zero_le _)) (fun _ _ => rfl)
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev F.glev0 (fun c => D.sp.crdLat0 (D.clsLat u 0 c))
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y_bij
      (fun c x => by rw [← clsCrd_zero]; exact (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y_lat c x)
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI_inj
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI_range
  obtain ⟨w, hw⟩ := exists_place (F := D.host.F) (D.host.g 0) (D.host.g_prime 0)
  refine ⟨{
    Lb := S.Lb
    Lb_fin := S.Lb_fin
    Lb_span := S.Lb_span
    Lb_int := S.Lb_int
    Lb_dual := S.Lb_dual
    Lb_index := S.Lb_index
    Uloc := S.Uloc
    Uloc_le := S.Uloc_le
    Uloc_lev := S.Uloc_lev
    Uloc_hyp := fun v h0 h1 hT => S.Uloc_hyp v (fun h => Or.elim h h0 h1) hT
    splitG := F.gl.sp
    splitG_sig := F.gl.sp_sig
    frG := L.fr
    Uloc_g := fun i v h x hx => mem_Uloc_iff_iwU S L le_rfl (rank_eq_first_level D.R).le i v h
      (fun hT => not_both_mem ((Nat.coprime_primes (D.mem u).A.T_prime (D.host.g_prime i)).2 (D.T_ne_g u i)) v hT h) x hx
    fM := S.fM
    fM_acg := S.fM_acg
    fM_mod := S.fM_mod
    fT := S.fT
    fT_ne := S.fT_ne
    fT_T := S.fT_T
    fM_card := S.fM_card
    fT_L := S.fT_L
    UlocAlt := S.UlocAlt
    U := S.U
    U_eq := S.U_eq
    U_compact := S.U_compact
    U_open := S.U_open
    w1 := w
    reflection_mem_Glev_castSucc := hw
    y := y
    y_bij := hbij
    y_lat := hlat
    stabI := st
    stabI_inj := hinj
    stabI_range := fun c γ hγ => hrange c ⟨γ, hγ⟩
    stabI_lat := fun c γ x => stab_class_lattice S _ (crdLat0_fin D u c) (crdLat0_span D u c) (y c).1 (hlat c)
      (st c γ).1 ((hrange c (st c γ)).1 ⟨γ, rfl⟩) x }, hcar, rfl, hfr⟩

set_option maxHeartbeats 4000000 in

theorem colLevel_of_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F →
  ∃ L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u),
    SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
      L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
      L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
      (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
      (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) ∧
    F.gl.sp = L.splitG ∧ ∀ i v h, F.glev0.fr i v h = reGL (rank_eq_first_level (I.rec7 l Z).R) _ (L.frG i v h) :=
  fun I _ _ l Z u _ _ F _ => exists_colLevel (I.rec7 l Z) u F

end GlobalTheory.Mem.LevZero
