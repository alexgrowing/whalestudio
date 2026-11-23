import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.EmptyFirstBlock

noncomputable section
namespace GlobalTheory.CompanionTheory.CellCongr
open Matrix

section Perm
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def permU (s : n ≃ n) : GL n R where
  val := s.toPEquiv.toMatrix
  inv := s.symm.toPEquiv.toMatrix
  val_inv := by
    rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_eq]
    ext i j
    simp [Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  inv_val := by
    rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_eq]
    ext i j
    simp [Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem permU_conj (s : n ≃ n) (M : GL n R) :
    permU s.symm * M * (permU s.symm)⁻¹ = reindexGL s M := by
  apply Units.ext
  show s.symm.toPEquiv.toMatrix * (M : Matrix n n R) * s.symm.symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl
end Perm

section Gen
variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

theorem twKer_le (ρ : Representation F G V) {N N' : Subgroup G} (x : G)
    (hN : ∀ u ∈ N, x * u * x⁻¹ ∈ N') :
    twKer ρ N 1 ≤ (twKer ρ N' 1).comap (ρ x) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨⟨_, hN u u.2⟩, ρ x v, ?_⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
  congr 1
  simp [← Module.End.mul_apply, ← map_mul]

def jacConj (ρ : Representation F G V) {N N' : Subgroup G} (x : G)
    (hN : ∀ u ∈ N, x * u * x⁻¹ ∈ N') (hN' : ∀ u ∈ N', x⁻¹ * u * x⁻¹⁻¹ ∈ N) :
    Jacquet ρ N ≃ₗ[F] Jacquet ρ N' :=
  LinearEquiv.ofLinear ((twKer ρ N 1).mapQ (twKer ρ N' 1) (ρ x) (twKer_le ρ x hN))
    ((twKer ρ N' 1).mapQ (twKer ρ N 1) (ρ x⁻¹) (twKer_le ρ x⁻¹ hN'))
    (by ext v; simp [← Module.End.mul_apply, ← map_mul])
    (by ext v; simp [← Module.End.mul_apply, ← map_mul])

theorem jacConj_mk (ρ : Representation F G V) {N N' : Subgroup G} (x : G)
    (hN : ∀ u ∈ N, x * u * x⁻¹ ∈ N') (hN' : ∀ u ∈ N', x⁻¹ * u * x⁻¹⁻¹ ∈ N) (v : V) :
    jacConj ρ x hN hN' (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ x v) := rfl

end Gen

section Ind
variable {F G V W : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

def indConj {H H' : Subgroup G} {σ : Representation F H V} {τ : Representation F H' W} (y : G)
    (J : V →ₗ[F] W)
    (h : ∀ q : H', ∃ p : H, (p : G) = y⁻¹ * q * y ∧ ∀ w, J (σ p w) = τ q (J w)) :
    smoothPart (ind H σ) →ₗ[F] smoothPart (ind H' τ) where
  toFun f := ⟨⟨fun a => J (f.1.1 (y⁻¹ * a)), fun q a => by
      obtain ⟨p, hp, hs⟩ := h q
      show J (f.1.1 (y⁻¹ * (q * a))) = τ q (J (f.1.1 (y⁻¹ * a)))
      rw [← hs, ← f.1.2 p, hp]
      congr 2
      group⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
      have hg' : ind H σ g f.1 = f.1 := hg
      apply Subtype.ext
      funext x
      have := congrFun (congrArg Subtype.val hg') (y⁻¹ * x)
      show J (f.1.1 (y⁻¹ * (x * g))) = J (f.1.1 (y⁻¹ * x))
      rw [← mul_assoc]
      exact congrArg J this)⟩
  map_add' _ _ := Subtype.ext (Subtype.ext (funext fun _ => map_add J _ _))
  map_smul' _ _ := Subtype.ext (Subtype.ext (funext fun _ => map_smul J _ _))

theorem smInd_conj {H H' : Subgroup G} {σ : Representation F H V} {τ : Representation F H' W} (y : G)
    (J : V ≃ₗ[F] W) (hH : ∀ p, p ∈ H ↔ y * p * y⁻¹ ∈ H')
    (hJ : ∀ (p : H) (q : H'), (q : G) = y * p * y⁻¹ → ∀ w, J (σ p w) = τ q (J w)) :
    Nonempty ((smInd H σ).Equiv (smInd H' τ)) := by
  have h1 : ∀ q : H', ∃ p : H, (p : G) = y⁻¹ * q * y ∧ ∀ w, J.toLinearMap (σ p w) = τ q (J.toLinearMap w) := by
    intro q
    have hp : y⁻¹ * (q : G) * y ∈ H := (hH _).2 (by simp [mul_assoc])
    exact ⟨⟨_, hp⟩, rfl, hJ ⟨_, hp⟩ q (by simp [mul_assoc])⟩
  have h2 : ∀ p : H, ∃ q : H', (q : G) = y⁻¹⁻¹ * p * y⁻¹ ∧
      ∀ w, J.symm.toLinearMap (τ q w) = σ p (J.symm.toLinearMap w) := by
    intro p
    refine ⟨⟨_, (hH p).1 p.2⟩, by simp, fun w => ?_⟩
    apply J.injective
    have := hJ p ⟨_, (hH p).1 p.2⟩ rfl (J.symm w)
    simpa using this.symm
  refine ⟨.mk (LinearEquiv.ofLinear (indConj y J.toLinearMap h1) (indConj y⁻¹ J.symm.toLinearMap h2) ?_ ?_)
    fun g => ?_⟩
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show J (J.symm (f.1.1 (y⁻¹⁻¹ * (y⁻¹ * x)))) = f.1.1 x
    simp
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show J.symm (J (f.1.1 (y⁻¹ * (y⁻¹⁻¹ * x)))) = f.1.1 x
    simp
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show J (f.1.1 (y⁻¹ * x * g)) = J (f.1.1 (y⁻¹ * (x * g)))
    rw [mul_assoc]
end Ind

section Block
variable {R : Type} [CommRing R] {n α : Type} [Fintype n] [DecidableEq n] [Fintype α] [LinearOrder α]
  {d d' : α → Type} [∀ a, Fintype (d a)] [∀ a, DecidableEq (d a)] [∀ a, Fintype (d' a)]
  [∀ a, DecidableEq (d' a)]

def sg (e : (Σ a, d a) ≃ n) (e' : (Σ a, d' a) ≃ n) (h : ∀ a, d a ≃ d' a) : n ≃ n :=
  e.symm.trans ((Equiv.sigmaCongrRight h).trans e')

omit [Fintype n] [DecidableEq n] [Fintype α] [LinearOrder α] [∀ a, Fintype (d a)]
  [∀ a, DecidableEq (d a)] [∀ a, Fintype (d' a)] [∀ a, DecidableEq (d' a)] in
@[simp] theorem sg_apply (e : (Σ a, d a) ≃ n) (e' : (Σ a, d' a) ≃ n) (h : ∀ a, d a ≃ d' a) (a : α)
    (i : d a) : sg e e' h (e ⟨a, i⟩) = e' ⟨a, h a i⟩ := by
  simp [sg]

omit [Fintype α] [LinearOrder α] [∀ a, Fintype (d a)] [∀ a, DecidableEq (d a)]
  [∀ a, Fintype (d' a)] [∀ a, DecidableEq (d' a)] in
theorem reindex_sg_apply (e : (Σ a, d a) ≃ n) (e' : (Σ a, d' a) ≃ n) (h : ∀ a, d a ≃ d' a)
    (g : GL n R) (a b : α) (i : d a) (j : d b) :
    (reindexGL (sg e e' h) g : Matrix n n R) (e' ⟨a, h a i⟩) (e' ⟨b, h b j⟩) =
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨b, j⟩) := by
  have h1 : ∀ (a : α) (i : d a), (sg e e' h).symm (e' ⟨a, h a i⟩) = e ⟨a, i⟩ := fun a i => by
    rw [Equiv.symm_apply_eq, sg_apply]
  rw [val_reindexGL, h1, h1]

def levR (R : Type) [CommRing R] (h : ∀ a, d a ≃ d' a) : Levi R d →* Levi R d' :=
  MonoidHom.pi fun a => (reindexGL (h a)).comp (Pi.evalMonoidHom (fun a => GL (d a) R) a)

theorem levR_apply (h : ∀ a, d a ≃ d' a) (t : Levi R d) (a : α) (i j : d a) :
    (levR R h t a : Matrix (d' a) (d' a) R) (h a i) (h a j) = (t a : Matrix (d a) (d a) R) i j := by
  show (reindexGL (h a) (t a) : Matrix (d' a) (d' a) R) (h a i) (h a j) = _
  rw [val_reindexGL]
  simp

theorem mem_parab_sg (e : (Σ a, d a) ≃ n) (e' : (Σ a, d' a) ≃ n) (h : ∀ a, d a ≃ d' a) (g : GL n R) :
    g ∈ parab R e ↔ reindexGL (sg e e' h) g ∈ parab R e' := by
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro H a b i j hab
    obtain ⟨i, rfl⟩ := (h a).surjective i
    obtain ⟨j, rfl⟩ := (h b).surjective j
    rw [reindex_sg_apply]
    exact H a b i j hab
  · intro H a b i j hab
    rw [← reindex_sg_apply e e' h]
    exact H a b _ _ hab

theorem mem_unipRad_sg (e : (Σ a, d a) ≃ n) (e' : (Σ a, d' a) ≃ n) (h : ∀ a, d a ≃ d' a) (g : GL n R) :
    g ∈ unipRad R e ↔ reindexGL (sg e e' h) g ∈ unipRad R e' := by
  rw [mem_unipRad, mem_unipRad, ← mem_parab_sg e e' h]
  refine and_congr Iff.rfl ⟨fun H a i j => ?_, fun H a i j => ?_⟩
  · obtain ⟨i, rfl⟩ := (h a).surjective i
    obtain ⟨j, rfl⟩ := (h a).surjective j
    rw [reindex_sg_apply, H a i j]
    simp [Matrix.one_apply]
  · rw [← reindex_sg_apply e e' h, H a]
    simp [Matrix.one_apply]

theorem leviProj_sg (e : (Σ a, d a) ≃ n) (e' : (Σ a, d' a) ≃ n) (h : ∀ a, d a ≃ d' a)
    (p : parab R e) (q : parab R e') (hq : (q : GL n R) = reindexGL (sg e e' h) p) :
    leviProj R e' q = levR R h (leviProj R e p) := by
  funext a
  ext i j
  obtain ⟨i, rfl⟩ := (h a).surjective i
  obtain ⟨j, rfl⟩ := (h a).surjective j
  rw [levR_apply, leviProj_apply, leviProj_apply, hq, reindex_sg_apply]

theorem leviEmb_sg (e : (Σ a, d a) ≃ n) (e' : (Σ a, d' a) ≃ n) (h : ∀ a, d a ≃ d' a) (t : Levi R d) :
    reindexGL (sg e e' h) (leviEmb R e t) = leviEmb R e' (levR R h t) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := e'.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e'.surjective y
  obtain ⟨i, rfl⟩ := (h a).surjective i
  obtain ⟨j, rfl⟩ := (h b).surjective j
  rw [reindex_sg_apply]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same, levR_apply]
  · rw [leviEmb_apply_ne R e _ hab, leviEmb_apply_ne R e' _ hab]

end Block

section Delta
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α]
  {d d' : α → Type} [∀ a, Fintype (d a)] [∀ a, DecidableEq (d a)] [∀ a, Fintype (d' a)]
  [∀ a, DecidableEq (d' a)]

theorem deltaHalf_levR (h : ∀ a, d a ≃ d' a) (t : Levi k d) :
    deltaHalf k d' (levR k h t) = deltaHalf k d t := by
  have hm : ∀ a, modExp d' a = modExp d a := fun a => by
    simp only [modExp, fun b => Fintype.card_congr (h b)]
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [hm]
  exact congrArg _ (det_reindexGL (h a) (t a))
end Delta

section Family
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c c' : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  [∀ i j, Fintype (c' i j)] [∀ i j, DecidableEq (c' i j)]

def xL (f : ∀ i, (Σ j, c i j) ≃ m i) (f' : ∀ i, (Σ j, c' i j) ≃ m i) (h : ∀ i j, c i j ≃ c' i j) :
    Levi k m :=
  fun i => permU (sg (f i) (f' i) (h i)).symm

def famR (k : Type) [Field k] (h : ∀ i j, c i j ≃ c' i j) :
    (∀ i, Levi k (c i)) →* ∀ i, Levi k (c' i) :=
  MonoidHom.pi fun i => (levR k (h i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

variable (f : ∀ i, (Σ j, c i j) ≃ m i) (f' : ∀ i, (Σ j, c' i j) ≃ m i) (h : ∀ i j, c i j ≃ c' i j)

theorem xL_conj (a : Levi k m) (i : α) :
    (xL f f' h * a * (xL f f' h)⁻¹ : Levi k m) i = reindexGL (sg (f i) (f' i) (h i)) (a i) :=
  permU_conj _ _

theorem mem_relParab_conj (p : Levi k m) :
    p ∈ relParab k f ↔ xL f f' h * p * (xL f f' h)⁻¹ ∈ relParab k f' := by
  simp only [relParab, Subgroup.mem_pi, xL_conj]
  exact forall₂_congr fun i _ => mem_parab_sg (f i) (f' i) (h i) (p i)

theorem mem_relUnip_conj (p : Levi k m) :
    p ∈ relUnip k f ↔ xL f f' h * p * (xL f f' h)⁻¹ ∈ relUnip k f' := by
  simp only [relUnip, Subgroup.mem_pi, xL_conj]
  exact forall₂_congr fun i _ => mem_unipRad_sg (f i) (f' i) (h i) (p i)

theorem relProj_conj (p : relParab k f) (q : relParab k f')
    (hq : (q : Levi k m) = xL f f' h * (p : Levi k m) * (xL f f' h)⁻¹) :
    relProj k f' q = famR k h (relProj k f p) := by
  funext i
  exact leviProj_sg (f i) (f' i) (h i) ⟨p.1 i, p.2 i trivial⟩ ⟨q.1 i, q.2 i trivial⟩
    ((congrFun hq i).trans (xL_conj f f' h _ i))

theorem relEmb_conj (g : ∀ i, Levi k (c i)) :
    xL f f' h * relEmb k f g * (xL f f' h)⁻¹ = relEmb k f' (famR k h g) := by
  funext i
  rw [xL_conj]
  exact leviEmb_sg (f i) (f' i) (h i) (g i)

omit [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] in
theorem relDeltaHalf_famR (h : ∀ i j, c i j ≃ c' i j) (g : ∀ i, Levi k (c i)) :
    relDeltaHalf k c' (famR k h g) = relDeltaHalf k c g := by
  rw [relDeltaHalf_apply, relDeltaHalf_apply]
  exact Finset.prod_congr rfl fun i _ => deltaHalf_levR (h i) (g i)

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def jacJ (ρ : Representation ℂ (Levi k m) W) :
    Jacquet ρ (relUnip k f) ≃ₗ[ℂ] Jacquet ρ (relUnip k f') :=
  jacConj ρ (xL f f' h) (fun u hu => (mem_relUnip_conj f f' h u).1 hu)
    (fun u hu => (mem_relUnip_conj f f' h _).2 (by simpa [mul_assoc] using hu))

theorem jacJ_relJac (ρ : Representation ℂ (Levi k m) W) (g : ∀ i, Levi k (c i))
    (w : Jacquet ρ (relUnip k f)) :
    jacJ f f' h ρ (relJac f ρ g w) = relJac f' ρ (famR k h g) (jacJ f f' h ρ w) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hx : ρ (xL f f' h) (ρ (relEmb k f g) v) =
      ρ (relEmb k f' (famR k h g)) (ρ (xL f f' h) v) := by
    rw [← relEmb_conj f f' h g, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    simp
  show jacJ f f' h ρ (relJac f ρ g (Submodule.Quotient.mk v)) =
    relJac f' ρ (famR k h g) (jacJ f f' h ρ (Submodule.Quotient.mk v))
  rw [relJac_mk, map_smul, jacJ, jacConj_mk, jacConj_mk, relJac_mk, relDeltaHalf_famR, hx]

theorem relInd_congr (σ : Representation ℂ (∀ i, Levi k (c i)) V)
    (τ : Representation ℂ (∀ i, Levi k (c' i)) W) (J : V ≃ₗ[ℂ] W)
    (hJ : ∀ g w, J (σ g w) = τ (famR k h g) (J w)) :
    Nonempty ((relInd f σ).Equiv (relInd f' τ)) := by
  refine smInd_conj (xL f f' h) J (mem_relParab_conj f f' h) fun p q hq w => ?_
  simp only [MonoidHom.comp_apply, twist_apply]
  rw [relProj_conj f f' h p q hq, map_smul, hJ, relDeltaHalf_famR]

end Family

theorem cellFunctor_congr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {c c' : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] [∀ i j, Fintype (c' i j)] [∀ i j, DecidableEq (c' i j)], (∀ i j, Fintype.card (c i j) = Fintype.card (c' i j)) → ∀ (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (f' : ∀ i, (Σ j, c' i j) ≃ m i) (g' : ∀ j, (Σ i, c' i j) ≃ m' j) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((cellFunctor f g ρ).Equiv (cellFunctor f' g' ρ)) := by
  intro k _ _ _ _ α β' _ _ _ _ m _ _ m' _ _ c c' _ _ _ _ hc f g f' g' W _ _ ρ
  let h : ∀ i j, c i j ≃ c' i j := fun i j => Fintype.equivOfCardEq (hc i j)
  exact relInd_congr (c := fun j i => c i j) (c' := fun j i => c' i j) g g' (fun j i => h i j) _ _
    (jacJ f f' h ρ) fun t w => jacJ_relJac f f' h ρ _ w

end GlobalTheory.CompanionTheory.CellCongr
