import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsEtaleFirstChernUntwisted
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.ConnAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.RedAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsFirstChernDeRhamUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem toV_ex (M : Model l K) (n : ℕ) (v : M.V n) : ∃ ζ : ℤ_[l], ζ ≠ 0 ∧ ∃ x : M.T n, (ζ : ℚ_[l]) • v = M.toV n x :=
  Inj.exists_int_mul (T := GlobalTheory.EtC.Hl l M.spc n 0) v

theorem sum_coord' {K B V V' V'' : Type _} [Field K] [CommRing B] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    [AddCommGroup V''] [Module K V''] (o : K →+* B) {m m' : ℕ} (b : Module.Basis (Fin m) K V) (b' : Module.Basis (Fin m') K V')
    (μ : V →ₗ[K] V' →ₗ[K] V'') (φ : Module.Dual K V'') (x : V) (y : V') :
    ∑ s, ∑ s', o (b.coord s x) * o (b'.coord s' y) * o (φ (μ (b s) (b' s'))) = o (φ (μ x y)) := by
  conv_rhs => rw [← b.sum_repr x, ← b'.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, Module.Basis.coord_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring

def Pure (P : HTPre l K) (M : Model l K) (a n : ℕ) (v : M.T n) (c : Hdg M.q a n) : Prop :=
  (∀ φ, P.h M a n (M.toV n v) φ = kC K (φ c)) ∧ ∀ a', a' ≠ a → ∀ φ, P.h M a' n (M.toV n v) φ = 0

def hb (P : HTPre l K) {M : Model l K} (hM : M.Sm) (n a : ℕ) :
    Module.Basis (Fin (Module.finrank K (Hdg M.q a n))) K (Hdg M.q a n) :=
  haveI := (P.fin M hM a n).1
  Module.finBasis _ _

theorem pure_cup (P : HTPre l K) (hF : KForm) {M : Model l K} (hM : M.Sm) {a b i j : ℕ} {x : M.T i} {y : M.T j}
    {z : M.T (i + j)} (hz : M.CupT x y z) {c : Hdg M.q a i} {c' : Hdg M.q b j} (hx : Pure P M a i x c) (hy : Pure P M b j y c') :
    Pure P M (a + b) (i + j) z (cupH M.q rfl rfl c c') := by
  classical
  constructor
  · intro φ
    rw [P.cup M hM x y z hz (hb P hM i) (hb P hM j) (a + b) φ]
    rw [Finset.sum_eq_single (⟨(a, b), Finset.HasAntidiagonal.mem_antidiagonal.2 rfl⟩ :
      (Finset.HasAntidiagonal.antidiagonal (a + b) : Finset (ℕ × ℕ)))]
    · obtain ⟨μ, hμ⟩ := hF.bilin M.q (rfl : a + b = a + b) (rfl : i + j = i + j)
      have := sum_coord' (kC K) (hb P hM i a) (hb P hM j b) μ φ c c'
      simp only [hμ] at this
      refine Eq.trans ?_ this
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
      exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (hx.1 _) (hy.1 _)) rfl
    · rintro ⟨⟨p, q⟩, hp⟩ _ hne
      have hp' : p + q = a + b := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
      by_cases h : p = a
      · have hq : q ≠ b := fun e => hne (Subtype.ext (Prod.ext h e))
        rw [hy.2 q hq, mul_zero, zero_mul]
      · rw [hx.2 p h, zero_mul, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro e he φ
    rw [P.cup M hM x y z hz (hb P hM i) (hb P hM j) e φ]
    refine Finset.sum_eq_zero ?_
    rintro ⟨⟨p, q⟩, hp⟩ _
    have hp' : p + q = e := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
    by_cases h : p = a
    · have hq : q ≠ b := fun e' => he (by omega)
      rw [hy.2 q hq, mul_zero, zero_mul]
    · rw [hx.2 p h, zero_mul, zero_mul]

theorem dual_zero {K V : Type _} [Field K] [AddCommGroup V] [Module K V] (h : Subsingleton V) (φ : Module.Dual K V) : φ = 0 :=
  LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]

theorem pure_pow (P : HTPre l K) (E : EtSide (Model.Sm (l := l) (K := K))) (hF : KForm) {M : Model l K} (hM : M.Sm)
    (o : M.T 0) (ho : ∀ k, o.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) {v : M.T 2} {c : Hdg M.q 1 2} (hv : Pure P M 1 2 v c) :
    ∀ k : ℕ, ∃ w : M.T (2 * k), Pure P M k (2 * k) w (powH M.q c k)
  | 0 => ⟨o, P.one M hM o ho, fun a ha φ => by
      rw [dual_zero ((P.fin M hM a 0).2 (Nat.pos_of_ne_zero ha)) φ, map_zero]⟩
  | k + 1 => by
    obtain ⟨w, hw⟩ := pure_pow P E hF hM o ho hv k
    obtain ⟨z, hz⟩ := E.cup_ex M w v
    exact ⟨z, pure_cup P hF hM hz hw hv⟩

theorem top_ne (P : HTPre l K) (E : EtSide (Model.Sm (l := l) (K := K))) (hT : KTop) (hF : KForm) {M : Model l K} (hM : M.Sm)
    (o : M.T 0) (ho : ∀ k, o.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) (d : ℕ) (hc : M.Conn d) :
    ∃ (v : M.V (2 * d)) (φ : Module.Dual K (Hdg M.q d (2 * d))), P.h M d (2 * d) v φ ≠ 0 := by
  have := hc.1
  have := hc.2
  obtain ⟨D, hD⟩ := Pb.isO1_exists M.p hM.1.1
  have hK : Pb.IsTautologicalLine M.q (genD D) := Pb.isTwistingSheaf_pullback (OK l K).subtype M.p D hD
  have he := Pb.isO1_etale hD
  obtain ⟨N, i, -, -, hi⟩ := hD
  have hs := Pb.sSup_𝒱D D N i hi
  obtain ⟨r⟩ := GlobalTheory.CompanionTheory.RootsC.rootsEx l
  obtain ⟨hv, c, hcc, -⟩ := P.first_chern_class_exists M hM D he hs
  obtain ⟨v, hv⟩ := hv r
  obtain ⟨w, hw⟩ := pure_pow P E hF hM o ho (P.c1 M hM D he hs r v c hv hcc) d
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (hT M.q d _ hK c hcc)
  exact ⟨_, φ, by rw [hw.1, hφ, map_one]; exact one_ne_zero⟩

theorem abs1 {B ι : Type _} [Field B] [Fintype ι] {κ κ' : ι → Type _} [∀ p, Fintype (κ p)] [∀ p, Fintype (κ' p)]
    (ζ x G : B) (hζ : ζ ≠ 0) (A : ∀ p, κ p → B) (Y : ∀ p, κ' p → B) (W : ∀ p, κ p → κ' p → B)
    (e : ζ * x * G = ∑ p, ∑ s, ∑ s', ζ * A p s * Y p s' * W p s s') : x * G = ∑ p, ∑ s, ∑ s', A p s * (Y p s' * W p s s') := by
  apply mul_left_cancel₀ hζ
  rw [← mul_assoc, e]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring

theorem abs2 {B ι α : Type _} [Field B] [Fintype ι] [Fintype α] {κ κ' : ι → Type _} [∀ p, Fintype (κ p)] [∀ p, Fintype (κ' p)]
    (z x : α → B) (G : B) (A : α → ∀ p, κ p → B) (W : ∀ p, κ p → κ' p → B)
    (hk : ∀ k, x k * G = ∑ p, ∑ s, ∑ s', A k p s * W p s s') (h : ∀ p s, κ' p → ∑ k, z k * A k p s = 0) :
    (∑ k, z k * x k) * G = 0 := by
  rw [Finset.sum_mul]
  simp only [mul_assoc, hk, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun s' _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, h p s s', zero_mul]

theorem key1 (P : HTPre l K) {M : Model l K} (hM : M.Sm) {i j d : ℕ} (v : M.V i)
    (g : M.V (i + j)) (y : M.T j) (f : Module.Dual ℚ_[l] (M.V i))
    (hf : ∀ x : M.T i, ∃ w, M.CupT x y w ∧ M.toV (i + j) w = f (M.toV i x) • g) (φ : Module.Dual K (Hdg M.q d (i + j))) :
    qC l (f v) * P.h M d (i + j) g φ =
      ∑ p : (Finset.HasAntidiagonal.antidiagonal d : Finset (ℕ × ℕ)), ∑ s, ∑ s', P.h M p.1.1 i v ((hb P hM i p.1.1).coord s) *
        (P.h M p.1.2 j (M.toV _ y) ((hb P hM j p.1.2).coord s') *
        kC K (φ (cupH M.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl (hb P hM i p.1.1 s) (hb P hM j p.1.2 s')))) := by
  obtain ⟨ζ, hζ, x, hx⟩ := toV_ex M i v
  obtain ⟨w, hw, hw'⟩ := hf x
  have e := P.cup M hM x y w hw (hb P hM i) (hb P hM j) d φ
  rw [hw', ← hx, P.lin, f.map_smul, smul_eq_mul, (qC l).map_mul] at e
  have hq : qC l (ζ : ℚ_[l]) ≠ 0 := (map_ne_zero (qC l)).mpr (fun h => hζ (Subtype.ext h))
  refine abs1 _ _ _ hq _ _ _ (e.trans ?_)
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  rw [P.lin]

theorem key0 (P : HTPre l K) {M : Model l K} (hM : M.Sm) {i j d : ℕ} {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V i))
    (z : Fin a → ℂ_[l]) (hz : ∀ p q, p + q = d → (∀ ψ, ∑ k, z k * P.h M p i (b k) ψ = 0) ∨ j < q)
    (g : M.V (i + j)) (y : M.T j) (f : Module.Dual ℚ_[l] (M.V i))
    (hf : ∀ x : M.T i, ∃ w, M.CupT x y w ∧ M.toV (i + j) w = f (M.toV i x) • g) (φ : Module.Dual K (Hdg M.q d (i + j))) :
    (∑ k, z k * qC l (f (b k))) * P.h M d (i + j) g φ = 0 := by
  refine abs2 z _ _ _ _ (fun k => key1 P hM (b k) g y f hf φ) fun p s s' => ?_
  rcases hz p.1.1 p.1.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) with h | h
  · exact h _
  · exact absurd (@Subsingleton.elim _ ((P.fin M hM p.1.2 j).2 h) (hb P hM j p.1.2 s') 0) ((hb P hM j p.1.2).ne_zero s')

theorem coords0 {F B V : Type _} [Field F] [Field B] (q : F →+* B) [AddCommGroup V] [Module F V] (A : Set (Module.Dual F V))
    (hA : Submodule.span F A = ⊤) {a : ℕ} (b : Module.Basis (Fin a) F V)
    (z : Fin a → B) (h : ∀ f ∈ A, ∑ k, z k * q (f (b k)) = 0) : z = 0 := by
  funext k0
  have hall : ∀ f ∈ Submodule.span F A, ∑ k, z k * q (f (b k)) = 0 := by
    intro f hf
    refine Submodule.span_induction (p := fun f _ => ∑ k, z k * q (f (b k)) = 0) ?_ ?_ ?_ ?_ hf
    · exact fun f hf => h f hf
    · simp
    · intro f f' _ _ h1 h2
      simp only [LinearMap.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      rw [h1, h2, add_zero]
    · intro c f _ h1
      have e : ∑ k, z k * q ((c • f) (b k)) = q c * ∑ k, z k * q (f (b k)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [LinearMap.smul_apply, smul_eq_mul, map_mul]
        ring
      show ∑ k, z k * q ((c • f) (b k)) = 0
      rw [e, h1, mul_zero]
  have := hall (b.coord k0) (by rw [hA]; trivial)
  have e : ∑ k, z k * q (b.coord k0 (b k)) = z k0 := by
    rw [Finset.sum_eq_single k0]
    · simp
    · intro k _ hk
      simp [Module.Basis.coord_apply, hk]
    · simp
  rwa [e] at this

theorem conn0 (P : HTPre l K) {M : Model l K} (hM : M.Sm) {d : ℕ} (hD : M.Dual d)
    (hne : ∃ (v : M.V (2 * d)) (φ : Module.Dual K (Hdg M.q d (2 * d))), P.h M d (2 * d) v φ ≠ 0) (n j : ℕ) (hj : n + j = 2 * d)
    {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (z : Fin a → ℂ_[l])
    (hz : ∀ p q, p + q = d → (∀ ψ, ∑ k, z k * P.h M p n (b k) ψ = 0) ∨ j < q) : z = 0 := by
  obtain ⟨r, g, hg, htr, hspan⟩ := hD.2 n j hj
  obtain ⟨v, φ, hu⟩ : ∃ (v : M.V (n + j)) (φ : Module.Dual K (Hdg M.q d (n + j))), P.h M d (n + j) v φ ≠ 0 := by
    have key : ∀ k, k = 2 * d → ∃ (v : M.V k) (φ : Module.Dual K (Hdg M.q d k)), P.h M d k v φ ≠ 0 := by
      rintro k rfl
      exact hne
    exact key _ hj
  have hv : v ∈ Submodule.span ℚ_[l] (Set.range g) := by rw [hg]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).mp hv
  obtain ⟨s0, hs0⟩ : ∃ s, P.h M d (n + j) (g s) φ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hu
    rw [← hc, map_sum, AddMonoidHom.finsetSum_apply]
    exact Finset.sum_eq_zero fun s _ => by rw [P.lin, hall, mul_zero]
  have hall : ∀ s, P.h M d (n + j) (g s) φ ≠ 0 := by
    intro s h0
    obtain ⟨σ, ζ, -, he⟩ := htr s0 s
    have := P.equi M hM d (n + j) σ (g s0) φ
    rw [he, P.lin, h0, mul_zero, mul_zero] at this
    exact hs0 ((map_eq_zero_iff _ (GaloisFrobeniusFixed.σC σ.1).injective).1 this.symm)
  refine coords0 (qC l) _ hspan b z ?_
  rintro f ⟨s, y, hf⟩
  exact (mul_eq_zero.mp (key0 P hM b z hz (g s) y f hf φ)).resolve_right (hall s)

theorem red_sum (P : HTPre l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (hM : M.Sm) (hN : N.Sm) (p n : ℕ)
    {a c : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (N.V n)) (e : Module.Basis (Fin c) ℚ_[l] (M.V n)) (z : Fin a → ℂ_[l])
    (φ : Module.Dual K (Hdg M.q p n)) :
    ∑ j, (∑ m, z m * qC l (e.coord j (Model.pullV u hu n (b m)))) * P.h M p n (e j) φ =
      ∑ m, z m * P.h N p n (b m) (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) p n) := by
  have hexp : ∀ v, P.h M p n v φ = ∑ j, qC l (e.coord j v) * P.h M p n (e j) φ := by
    intro v
    conv_lhs => rw [← e.sum_repr v]
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    simp only [P.lin, Module.Basis.coord_apply]
  simp_rw [← P.nat M N u hu hM hN, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hexp (Model.pullV u hu n (b m)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem reduce (P : HTPre l K) (hE : EtSide (Model.Sm (l := l) (K := K)))
    (hconn : ∀ M : Model l K, M.Sm → ∀ d, M.Conn d → ∀ n, P.Inj M n) (M : Model l K) (hM : M.Sm) (n : ℕ) : P.Inj M n := by
  obtain ⟨r, Q, d, u, hu, hQ, hinj⟩ := hE.comp M hM
  have : ∀ a, FiniteDimensional ℚ_[l] ((Q a).V n) := fun a => hE.fin _ (hQ a).1 n
  let e : ∀ a, Module.Basis (Fin (Module.finrank ℚ_[l] ((Q a).V n))) ℚ_[l] ((Q a).V n) :=
    fun a => Module.finBasis _ _
  let f : (Σ a, Fin (Module.finrank ℚ_[l] ((Q a).V n))) → Module.Dual ℚ_[l] (M.V n) :=
    fun i => (e i.1).coord i.2 ∘ₗ Model.pullV (u i.1) (hu i.1) n
  have hf : ∀ v, (∀ i, f i v = 0) → v = 0 := by
    intro v hv
    refine hinj n v fun a => (e a).ext_elem fun j => ?_
    simpa [f, Module.Basis.coord_apply] using hv ⟨a, j⟩
  intro c b z hz
  funext m
  have hm := Inj.red_abs (qC l) ⊥ (fun x s hs => by rw [AddSubgroup.mem_bot] at hs ⊢; rw [hs, mul_zero]) f hf b z ?_ m
  · simpa using hm
  rintro ⟨a, j⟩
  have hc := hconn (Q a) (hQ a).1 (d a) (hQ a).2 n (e a) (fun j => ∑ m, z m * qC l (f ⟨a, j⟩ (b m))) (fun p φ => by
    have h := hz p (φ ∘ₗ pullH (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a)) p n)
    rw [← red_sum P (u a) (hu a) (hQ a).1 hM p n b (e a) z φ] at h
    exact h)
  rw [AddSubgroup.mem_bot]
  exact congrFun hc j

theorem inj_of (P : HTPre l K) (E : EtSide (Model.Sm (l := l) (K := K))) (hT : KTop) (hF : KForm)
    (h1 : ∀ M : Model l K, ∃ v : M.T 0, ∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) :
    ∀ M : Model l K, M.Sm → (∀ n, P.Inj M n) ∧ ∀ d, M.Conn d → P.Top M d := by
  have hne := fun (M : Model l K) (hM : M.Sm) d (hc : M.Conn d) => (h1 M).elim fun o ho => top_ne P E hT hF hM o ho d hc
  intro M hM
  refine ⟨reduce P E (fun M hM d hc n => ?_) M hM, fun d hc => ?_⟩
  · intro k b z hz
    have hD := E.dual M hM d hc
    by_cases hn : 2 * d < n
    · have := hD.1 n hn
      exact funext fun i => absurd (Subsingleton.elim (b i) 0) (b.ne_zero i)
    · exact conn0 P hM hD (hne M hM d hc) n (2 * d - n) (by omega) b z fun p q _ => Or.inl (hz p)
  · intro k b z hz
    refine conn0 P hM (E.dual M hM d hc) (hne M hM d hc) (2 * d) 0 rfl b z fun p q h => ?_
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · obtain rfl : p = d := h
      exact Or.inl hz
    · exact Or.inr hq

end CrystallineSemistableComparison.HT
