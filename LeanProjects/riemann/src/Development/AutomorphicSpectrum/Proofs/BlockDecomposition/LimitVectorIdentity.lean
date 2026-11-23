import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRescaledConvergentSubsequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalPairTypedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSpaceCarriesFlatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistAbsoluteCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableInducedSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedDiscreteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedNodeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunctionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesInducedNodeStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

section Tree

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def indFin {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) :=
  Submodule.span ℂ {φ | MemInd2 U₁ U₂ φ ∧ φ ∈ finVec (cptRep E (r + s))}

theorem indFin_le {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : indFin U₁ U₂ ≤ indSpan U₁ U₂ :=
  Submodule.span_mono fun _ h => h.1

theorem memInd2_of_indSpan {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indSpan U₁ U₂) : MemInd2 U₁ U₂ φ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => add_mem (hx.2 k g) (hy.2 k g)⟩
    change x.1 _ + y.1 _ = x.1 g + y.1 g
    rw [hx.1, hy.1]
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => Submodule.smul_mem _ c (hx.2 k g)⟩
    change c * x.1 _ = c * x.1 g
    rw [hx.1]

theorem finVec_of_indFin {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indFin U₁ U₂) : φ ∈ finVec (cptRep E (r + s)) :=
  (Submodule.span_le (p := finVec (cptRep E (r + s)))).2 (fun _ hx => hx.2) h

theorem mem_indFin {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h₁ : MemInd2 U₁ U₂ φ) (h₂ : φ ∈ finVec (cptRep E (r + s))) : φ ∈ indFin U₁ U₂ :=
  Submodule.subset_span ⟨h₁, h₂⟩

theorem finStable_indFin {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    FinStable (indFin U₁ U₂) := by
  intro g φ hφ
  refine mem_indFin (memInd2_of_indSpan (GlobalTheory.T.finStable_induced_span U₁ U₂ g φ (indFin_le _ _ hφ))) ?_
  have h1 := finVec_rt (finVec_of_indFin hφ) 1 g
  have e : rt E (r + s) (cf (r + s) 1 g) φ = act (.fin g) φ := by
    refine Subtype.ext (funext fun x => ?_)
    rw [cf, show (Unitary.toUnits (1 : Kinf E (r + s))) = 1 from map_one _, map_one, one_mul]
    rfl
  rwa [e] at h1

theorem mul_mem_Sm {N : ℕ} {e f : GA E N → ℂ} (he : e ∈ Sm E N) (hf : f ∈ Sm E N) : (fun x => e x * f x) ∈ Sm E N := by
  intro g
  refine ((he g).mul (hf g)).congr fun x hx => ?_
  have hx' : IsUnit (Matrix.of x) := hx
  simp [chart, hx']

def mulOp {N : ℕ} {e : GA E N → ℂ} (he : e ∈ Sm E N) : Sm E N →ₗ[ℂ] Sm E N where
  toFun φ := ⟨fun x => e x * φ.1 x, mul_mem_Sm he φ.2⟩
  map_add' φ ψ := Subtype.ext (funext fun x => mul_add _ _ _)
  map_smul' c φ := Subtype.ext (funext fun x => mul_left_comm _ _ _)

theorem carries_indFin {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (U₁ U₁' : Submodule ℂ (Sm E r))
    (U₂ U₂' : Submodule ℂ (Sm E s)) (h₁ : FlatFn e₁) (h₂ : FlatFn e₂) (a₁ : FinStable U₁) (a₁' : FinStable U₁')
    (a₂ : FinStable U₂) (a₂' : FinStable U₂') (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂') :
    Carries (nodeFn e₁ e₂) (indFin U₁ U₂) (indFin U₁' U₂') := by
  intro φ hφ
  obtain ⟨φ', h', he⟩ := GlobalTheory.T.carries_induced_node e₁ e₂ U₁ U₁' U₂ U₂' h₁ h₂ a₁ a₁' a₂ a₂' c₁ c₂ φ (indFin_le _ _ hφ)
  refine ⟨φ', mem_indFin (memInd2_of_indSpan h') ?_, he⟩
  have hF := GlobalTheory.T.flat_node_function e₁ e₂ h₁ h₂
  have hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k φ)) := finVec_of_indFin hφ
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k φ)).map (mulOp hF.sm)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine ⟨cptRep E (r + s) k φ, Submodule.subset_span ⟨k, rfl⟩, Subtype.ext (funext fun x => ?_)⟩
  have e0 : x * infGL E (r + s) (Unitary.toUnits k) = x * cf (r + s) k 1 := by
    rw [cf, map_one, mul_one]
  change nodeFn e₁ e₂ x * φ.1 (x * infGL E (r + s) (Unitary.toUnits k)) =
    φ'.1 (x * infGL E (r + s) (Unitary.toUnits k))
  rw [he, e0, hF.rinv x k 1 (one_mem _)]

theorem fd_rank_zero (U : Submodule ℂ (Sm E 0)) : FiniteDimensional ℂ U := by
  haveI : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  haveI : Finite (GA E 0) := Finite.of_subsingleton
  infer_instance
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem strip_node_inv {r s : ℕ} (a : Tr E r) (b : Tr E s) : ∀ {N : ℕ} (u : Tr E N), N = r + s →
    HEq u.strip (Tr.node a.strip b.strip) → ∃ (u₁ : Tr E r) (u₂ : Tr E s), HEq u (Tr.node u₁ u₂) ∧
      u₁.strip = a.strip ∧ u₂.strip = b.strip := by
  intro N u
  cases u with
  | leaf V z =>
    intro hN h
    exact Tr.noConfusion rfl HEq.rfl HEq.rfl HEq.rfl hN h
  | @node r' s' u₁ u₂ =>
    intro hN h
    simp only [Tr.strip] at h
    refine Tr.noConfusion rfl HEq.rfl HEq.rfl HEq.rfl hN h fun hr hs h₁ h₂ => ?_
    subst hr hs
    exact ⟨u₁, u₂, HEq.rfl, eq_of_heq h₁, eq_of_heq h₂⟩

theorem strip_node {r s : ℕ} (a : Tr E r) (b : Tr E s) (u : Tr E (r + s)) (h : u.strip = (Tr.node a b).strip) :
    ∃ (u₁ : Tr E r) (u₂ : Tr E s), u = Tr.node u₁ u₂ ∧ u₁.strip = a.strip ∧ u₂.strip = b.strip := by
  obtain ⟨u₁, u₂, h1, h2, h3⟩ := strip_node_inv a b u rfl (heq_of_eq h)
  exact ⟨u₁, u₂, eq_of_heq h1, h2, h3⟩

theorem strip_leaf {N : ℕ} (V : Submodule ℂ (Sm E N)) (z : ℂ) (u : Tr E N) (h : u.strip = (Tr.leaf V z).strip) :
    ∃ z', u = Tr.leaf V z' := by
  have key : ∀ {M : ℕ} (u : Tr E M), ∀ (hM : M = N), HEq u.strip (Tr.leaf V (0 : ℂ)) → ∃ z', HEq u (Tr.leaf V z') := by
    intro M u
    cases u with
    | leaf V' z' =>
      intro hM h
      simp only [Tr.strip] at h
      refine Tr.noConfusion rfl HEq.rfl HEq.rfl HEq.rfl hM h fun hn hV _ => ?_
      subst hn
      obtain rfl := eq_of_heq hV
      exact ⟨z', HEq.rfl⟩
    | node u₁ u₂ =>
      intro hM h
      exact Tr.noConfusion rfl HEq.rfl HEq.rfl HEq.rfl hM h
  obtain ⟨z', h1⟩ := key u rfl (heq_of_eq h)
  exact ⟨z', eq_of_heq h1⟩

theorem disc_of_good {N : ℕ} (s : Tr E N) : s.Good → s.Disc := by
  induction s with
  | leaf V z =>
    intro h
    simp only [Tr.Good] at h
    simp only [Tr.Disc]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1⟩
  | node a b iha ihb =>
    intro h
    simp only [Tr.Good] at h
    simp only [Tr.Disc]
    exact ⟨iha h.1, ihb h.2⟩

theorem space_leaf {N : ℕ} (V : Submodule ℂ (Sm E N)) (z : ℂ) : (Tr.leaf V z).space = tw V z := by
  rw [Tr.space]

theorem space_node {r s : ℕ} (a : Tr E r) (b : Tr E s) :
    (Tr.node a b).space = indFin (tw a.space ((s : ℂ) / 2)) (tw b.space (-(r : ℂ) / 2)) := by
  rw [Tr.space]
  rfl

theorem treestable {N : ℕ} (t : Tr E N) : t.Disc → FinStable t.space := by
  induction t with
  | leaf V z =>
    intro ht
    simp only [Tr.Disc] at ht
    rw [space_leaf]
    rcases ht with ⟨-, rfl, -⟩ | ht
    · exact GlobalTheory.T.finStable_twist _ z fun _ _ _ => trivial
    · exact GlobalTheory.T.finStable_twist V z fun g φ hφ => ht.2.stable (.fin g) φ hφ
  | node a b _ _ =>
    intro _
    rw [space_node]
    exact finStable_indFin _ _

theorem treefd {N : ℕ} (t : Tr E N) : t.Disc → ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)),
    IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed t.space K W) := by
  induction t with
  | leaf V z =>
    intro ht
    simp only [Tr.Disc] at ht
    rw [space_leaf]
    rcases ht with ⟨rfl, -, -⟩ | ht
    · intro K W _ _
      exact fd_rank_zero _
    · exact GlobalTheory.T.finiteDimensional_typed_extension V z fun K W hK hW => GlobalTheory.T.finiteDimensional_typed_discrete V K W ht.2 hK hW
  | @node r' s' a b iha ihb =>
    intro ht
    simp only [Tr.Disc] at ht
    rw [space_node]
    intro K W hK hW
    haveI := GlobalTheory.T.finiteDimensional_typed_node (tw a.space ((s' : ℂ) / 2)) (tw b.space (-(r' : ℂ) / 2)) (GlobalTheory.T.finiteDimensional_typed_extension _ _ (iha ht.1))
      (GlobalTheory.T.finiteDimensional_typed_extension _ _ (ihb ht.2)) K W hK hW
    have hle : typed (indFin (tw a.space ((s' : ℂ) / 2)) (tw b.space (-(r' : ℂ) / 2))) K W ≤
        typed (indSpan (tw a.space ((s' : ℂ) / 2)) (tw b.space (-(r' : ℂ) / 2))) K W :=
      inf_le_inf_right _ (indFin_le _ _)
    exact Submodule.finiteDimensional_of_le hle

theorem twists_length {N : ℕ} (s : Tr E N) : ∀ (t : Tr E N), t.strip = s.strip → t.twists.length = s.twists.length := by
  induction s with
  | leaf V z =>
    intro t h
    obtain ⟨z', rfl⟩ := strip_leaf V z t h
    rfl
  | node a b iha ihb =>
    intro t h
    obtain ⟨u₁, u₂, rfl, h1, h2⟩ := strip_node a b t h
    simp only [Tr.twists, List.length_append, iha _ h1, ihb _ h2]

theorem treeflat {N : ℕ} (s : Tr E N) : ∀ (t : ℕ → Tr E N), s.Disc → (∀ k, (t k).Disc) → (∀ k, (t k).strip = s.strip) →
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0))) →
    ∃ e : ℕ → GA E N → ℂ, (∀ k, FlatFn (e k)) ∧ (∀ k, Carries (e k) (t k).space s.space) ∧
      ∀ x, Tendsto (fun k => e k x) atTop (𝓝 1) := by
  induction s with
  | @leaf M V z =>
    intro t _ _ hst hz
    choose zk hzk using fun k => strip_leaf V z (t k) (hst k)
    obtain rfl : t = fun k => Tr.leaf V (zk k) := funext hzk
    refine ⟨fun k => absFn M (z - zk k), fun k => GlobalTheory.T.flat_absolute_character M _, fun k => ?_, fun x => ?_⟩
    · simp only [space_leaf]
      exact GlobalTheory.T.carries_twist_absolute_character V (zk k) z
    · refine GlobalTheory.T.tendsto_absolute_character_one M x _ ?_
      have h0 := hz 0
      simp only [Tr.twists, List.getD_cons_zero] at h0
      simpa using (tendsto_const_nhds (x := z)).sub h0
  | @node r s' a b iha ihb =>
    intro t hs ht hst hz
    simp only [Tr.Disc] at hs
    choose u₁ u₂ hu h1 h2 using fun k => strip_node a b (t k) (hst k)
    obtain rfl : t = fun k => Tr.node (u₁ k) (u₂ k) := funext hu
    simp only [Tr.Disc] at ht
    have hd₁ : ∀ k, (u₁ k).Disc := fun k => (ht k).1
    have hd₂ : ∀ k, (u₂ k).Disc := fun k => (ht k).2
    have hl₁ : ∀ k, (u₁ k).twists.length = a.twists.length := fun k => twists_length a _ (h1 k)
    have hz₁ : ∀ i, Tendsto (fun k => ((u₁ k).twists.getD i 0)) atTop (𝓝 (a.twists.getD i 0)) := by
      intro i
      by_cases hi : i < a.twists.length
      · have h3 := hz i
        simp only [Tr.twists] at h3
        rw [List.getD_append _ _ _ _ hi] at h3
        exact h3.congr fun k => List.getD_append _ _ _ _ (by rw [hl₁]; exact hi)
      · have e1 : ∀ k, (u₁ k).twists.getD i 0 = 0 := fun k =>
          List.getD_eq_default _ _ (by rw [hl₁]; omega)
        rw [List.getD_eq_default _ _ (by omega)]
        simp only [e1]
        exact tendsto_const_nhds
    have hz₂ : ∀ i, Tendsto (fun k => ((u₂ k).twists.getD i 0)) atTop (𝓝 (b.twists.getD i 0)) := by
      intro i
      have h3 := hz (a.twists.length + i)
      simp only [Tr.twists] at h3
      rw [List.getD_append_right _ _ _ _ (by omega)] at h3
      simp only [Nat.add_sub_cancel_left] at h3
      refine h3.congr fun k => ?_
      rw [List.getD_append_right _ _ _ _ (by rw [hl₁]; omega), hl₁]
      simp only [Nat.add_sub_cancel_left]
    obtain ⟨e₁, he₁, hc₁, hl₁'⟩ := iha u₁ hs.1 hd₁ h1 hz₁
    obtain ⟨e₂, he₂, hc₂, hl₂'⟩ := ihb u₂ hs.2 hd₂ h2 hz₂
    refine ⟨fun k => nodeFn (e₁ k) (e₂ k), fun k => GlobalTheory.T.flat_node_function _ _ (he₁ k) (he₂ k), fun k => ?_, fun x => ?_⟩
    · rw [space_node, space_node]
      exact carries_indFin _ _ _ _ _ _ (he₁ k) (he₂ k) (GlobalTheory.T.finStable_twist _ _ (treestable _ (hd₁ k)))
        (GlobalTheory.T.finStable_twist _ _ (treestable _ hs.1)) (GlobalTheory.T.finStable_twist _ _ (treestable _ (hd₂ k)))
        (GlobalTheory.T.finStable_twist _ _ (treestable _ hs.2)) (GlobalTheory.T.carries_twist _ _ _ _ (hc₁ k)) (GlobalTheory.T.carries_twist _ _ _ _ (hc₂ k))
    · have h3 := (hl₁' (leviOf x).1).mul (hl₂' (leviOf x).2)
      rw [one_mul] at h3
      exact h3

end Tree

theorem limVec : PositivityTheory.Rg.BcB.SpectralAccumulation.LimVec := by
  intro _ E _ _ _ a b ι _ t₁ t₂ s₁ s₂ K₁ K₂ W₁ W₂ C lam lam₀ f hK₁ hK₂ hW₁ hW₂ _hC hs₁ hs₂ hd₁ hd₂ hst₁ hst₂ hz₁ hz₂
    hf0 hfm hfT hfe hlam
  have hD₁ : s₁.Disc := disc_of_good s₁ hs₁
  have hD₂ : s₂.Disc := disc_of_good s₂ hs₂
  obtain ⟨e₁, he₁, hc₁, hl₁⟩ := treeflat s₁ t₁ hD₁ hd₁ hst₁ hz₁
  obtain ⟨e₂, he₂, hc₂, hl₂⟩ := treeflat s₂ t₂ hD₂ hd₂ hst₂ hz₂
  have hO₁ : IsOpen ((K₁ ⊓ KO E a : Subgroup _) : Set (GL (Fin a) (Af E))) :=
    hK₁.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)
  have hO₂ : IsOpen ((K₂ ⊓ KO E b : Subgroup _) : Set (GL (Fin b) (Af E))) :=
    hK₂.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E b)
  let X : Submodule ℂ (H E a b → ℂ) :=
    pairSpace s₁.space s₂.space ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂
  haveI : FiniteDimensional ℂ X :=
    GlobalTheory.T.finiteDimensional_pair_typed _ _ _ _ _ _ (treefd s₁ hD₁ _ _ hO₁ hW₁) (treefd s₂ hD₂ _ _ hO₂ hW₂)
  let EE : ℕ → H E a b → ℂ := fun k x => e₁ k x.1 * e₂ k x.2
  have hEne : ∀ k x, EE k x ≠ 0 := fun k x => mul_ne_zero ((he₁ k).ne _) ((he₂ k).ne _)
  have hmem : ∀ k i, (fun x => EE k x * f k i x) ∈ X := fun k i =>
    GlobalTheory.T.pair_space_carries_flat (e₁ k) (e₂ k) _ _ _ _ K₁ K₂ W₁ W₂ _ (he₁ k) (he₂ k) (hc₁ k) (hc₂ k) (hfm k i) (hfT k i)
  let gM : ℕ → (ι → X) := fun k i => ⟨_, hmem k i⟩
  have hne : ∀ k, gM k ≠ 0 := by
    intro k h
    apply hf0 k
    funext i x
    have h1 : EE k x * f k i x = 0 := congrFun (congrArg Subtype.val (congrFun h i)) x
    exact (mul_eq_zero.1 h1).resolve_left (hEne k x)
  obtain ⟨c, φ, G, hφ, hG, hlim⟩ := GlobalTheory.T.exists_rescaled_convergent_subsequence gM hne
  let F : ι → H E a b → ℂ := fun i => (G i).1
  have hev : ∀ i x, Tendsto (fun k => c k * (EE (φ k) x * f (φ k) i x)) atTop (𝓝 (F i x)) := by
    intro i x
    exact hlim ((LinearMap.proj x) ∘ₗ X.subtype ∘ₗ (LinearMap.proj i))
  have hE1 : ∀ x, Tendsto (fun k => EE (φ k) x) atTop (𝓝 1) := fun x => by
    have h1 := (hl₁ x.1).mul (hl₂ x.2)
    rw [one_mul] at h1
    exact h1.comp hφ.tendsto_atTop
  have hft : ∀ i x, Tendsto (fun k => c k * f (φ k) i x) atTop (𝓝 (F i x)) := by
    intro i x
    have h2 := ((hE1 x).inv₀ one_ne_zero).mul (hev i x)
    simp only [inv_one, one_mul] at h2
    refine h2.congr fun k => ?_
    have h3 := hEne (φ k) x
    field_simp
  refine ⟨F, ?_, fun i => (G i).2.1, fun i => ⟨?_, (G i).2.2.2⟩, fun h hh => ?_⟩
  · intro h
    apply hG
    funext i
    exact Subtype.ext (congrFun h i)
  · intro u₁ hu₁ u₂ hu₂ x
    refine tendsto_nhds_unique (hft i _) ((hft i x).congr fun k => ?_)
    rw [(hfT _ i).1 u₁ hu₁ u₂ hu₂ x]
  · funext i x
    have hA : Tendsto (fun k => heckeAct h (fun j y => c k * f (φ k) j y) i x) atTop (𝓝 (heckeAct h F i x)) := by
      simp only [heckeAct, Finsupp.sum]
      exact tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun g _ => (hft j _).const_mul _
    have hB : ∀ k, heckeAct h (fun j y => c k * f (φ k) j y) i x = lam (φ k) h * (c k * f (φ k) i x) := by
      intro k
      have h1 : heckeAct h (f (φ k)) i x = lam (φ k) h * f (φ k) i x :=
        congrFun (congrFun (hfe (φ k) h hh) i) x
      have h2 : heckeAct h (fun j y => c k * f (φ k) j y) i x = c k * heckeAct h (f (φ k)) i x := by
        simp only [heckeAct, Finsupp.sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => ?_
        ring
      rw [h2, h1]
      ring
    have hC : Tendsto (fun k => lam (φ k) h * (c k * f (φ k) i x)) atTop (𝓝 (lam₀ h * F i x)) :=
      ((hlam h hh).comp hφ.tendsto_atTop).mul (hft i x)
    exact tendsto_nhds_unique (hA.congr hB) hC

end GlobalTheory.CompanionTheory.LimV

end
