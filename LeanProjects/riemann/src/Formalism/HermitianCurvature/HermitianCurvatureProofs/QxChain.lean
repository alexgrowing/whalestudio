import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRWeyl

noncomputable section

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace HatData
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {H : HatData X}

theorem hat_congr {T S : X → X} (hT : H.Good T) (hS : H.Good S) (h : ∀ x ∈ H.G, H.N (T x) = H.N (S x)) :
    H.hat T = H.hat S := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [hat_apply hT, hat_apply hS]
  exact h _ v.2.1

theorem good_sum {ι : Type*} (s : Finset ι) {T : ι → X → X} (hT : ∀ j ∈ s, H.Good (T j)) :
    H.Good (fun x => ∑ j ∈ s, T j x) := by
  classical
  revert hT
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact good_zero
  · intro j s hj ih hT
    simp only [Finset.sum_insert hj]
    exact (hT j (Finset.mem_insert_self j s)).add (ih fun i hi => hT i (Finset.mem_insert_of_mem hi))

theorem hat_sum {ι : Type*} (s : Finset ι) {T : ι → X → X} (hT : ∀ j ∈ s, H.Good (T j)) :
    H.hat (fun x => ∑ j ∈ s, T j x) = ∑ j ∈ s, H.hat (T j) := by
  classical
  revert hT
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact hat_zero
  · intro j s hj ih hT
    have hs : ∀ i ∈ s, H.Good (T i) := fun i hi => hT i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert hj]
    rw [hat_add (hT j (Finset.mem_insert_self j s)) (good_sum s hs), ih hs]

theorem good_foldr (L : List (X → X)) (hL : ∀ T ∈ L, H.Good T) : H.Good (fun x => L.foldr (fun T h => T h) x) := by
  induction L with
  | nil => exact good_id
  | cons T L ih =>
    exact (hL T (by simp)).comp (ih fun S hS => hL S (by simp [hS]))

theorem hat_foldr (L : List (X → X)) (hL : ∀ T ∈ L, H.Good T) :
    H.hat (fun x => L.foldr (fun T h => T h) x) = (L.map H.hat).prod := by
  induction L with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.prod_nil]
    exact hat_id
  | cons T L ih =>
    have hL' : ∀ S ∈ L, H.Good S := fun S hS => hL S (by simp [hS])
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [hat_comp (hL T (by simp)) (good_foldr L hL'), ih hL']

def Rep (H : HatData X) (T : X → X) (b : Module.End ℂ H.V) : Prop := H.Good T ∧ H.hat T = b

theorem Rep.comp {T S : X → X} {b b' : Module.End ℂ H.V} (h : Rep H T b) (h' : Rep H S b') :
    Rep H (fun x => T (S x)) (b * b') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  exact And.intro (h1.comp h1') (by rw [hat_comp h1 h1', h2, h2'])

theorem Rep.add {T S : X → X} {b b' : Module.End ℂ H.V} (h : Rep H T b) (h' : Rep H S b') :
    Rep H (fun x => T x + S x) (b + b') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  exact And.intro (h1.add h1') (by rw [hat_add h1 h1', h2, h2'])

theorem Rep.sub {T S : X → X} {b b' : Module.End ℂ H.V} (h : Rep H T b) (h' : Rep H S b') :
    Rep H (fun x => T x - S x) (b - b') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  exact And.intro (h1.sub h1') (by rw [hat_sub h1 h1', h2, h2'])

theorem Rep.neg {T : X → X} {b : Module.End ℂ H.V} (h : Rep H T b) : Rep H (fun x => -T x) (-b) := by
  obtain ⟨h1, h2⟩ := h
  exact And.intro h1.neg (by rw [hat_neg h1, h2])

theorem Rep.smul {T : X → X} {b : Module.End ℂ H.V} (h : Rep H T b) (a : ℂ) : Rep H (fun x => a • T x) (a • b) := by
  obtain ⟨h1, h2⟩ := h
  exact And.intro (h1.smul a) (by rw [hat_smul h1 a, h2])

theorem rep_id : Rep H (fun x => x) 1 := And.intro good_id hat_id

theorem rep_zero : Rep H (fun _ => (0 : X)) 0 := And.intro good_zero hat_zero

theorem Rep.sum {ι : Type*} (s : Finset ι) {T : ι → X → X} {b : ι → Module.End ℂ H.V}
    (h : ∀ j ∈ s, Rep H (T j) (b j)) : Rep H (fun x => ∑ j ∈ s, T j x) (∑ j ∈ s, b j) := by
  have hg : ∀ j ∈ s, H.Good (T j) := fun j hj => (h j hj).1
  refine And.intro (good_sum s hg) ?_
  rw [hat_sum s hg]
  exact Finset.sum_congr rfl (fun j hj => (h j hj).2)

theorem Rep.apply {T : X → X} {b : Module.End ℂ H.V} (h : Rep H T b) {x : X} (hx : x ∈ H.G) :
    H.N (T x) = ((b (H.toV x hx) : H.V) : X) := by
  obtain ⟨h1, h2⟩ := h
  subst h2
  rw [hat_toV h1 hx]
  rfl

end HatData

variable {k r : ℕ}

section Lev
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

open Classical in

def cut0 (i : Fin (r + 1)) (D : Set (Mx k r)) : (Mx k r → E) →ₗ[ℂ] (Mx k r → E) where
  toFun := fun f g => if g ∈ Glev k r i ∩ D then f g else 0
  map_add' := fun f f' => by
    funext g
    by_cases h : g ∈ Glev k r i ∩ D
    · simp only [Pi.add_apply, if_pos h]
    · simp only [Pi.add_apply, if_neg h, add_zero]
  map_smul' := fun s f => by
    funext g
    by_cases h : g ∈ Glev k r i ∩ D
    · simp only [Pi.smul_apply, if_pos h, RingHom.id_apply]
    · simp only [Pi.smul_apply, if_neg h, RingHom.id_apply, smul_zero]

theorem level_restriction_apply_on (f : Mx k r → E) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : cut0 i D f g = f g := by
  simp only [cut0, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h'
  rfl

theorem level_restriction_eq_iff (f f' : Mx k r → E) : cut0 i D f = cut0 i D f' ↔ ∀ g ∈ Glev k r i ∩ D, f g = f' g := by
  constructor
  · intro h g hg
    rw [← level_restriction_apply_on f hg, ← level_restriction_apply_on f' hg, h]
  · intro h
    funext g
    simp only [cut0, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with hg
    · exact h g hg
    · rfl

def levData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin (r + 1)) {D : Set (Mx k r)}
    (hD : IsOpen D) : HatData (Mx k r → E) where
  G := { carrier := {f | SmoothLev k r i D f}
         zero_mem' := Qx2.smooth_zero
         add_mem' := fun h h' => Qx2.smooth_add h h'
         smul_mem' := fun s _ h => Qx2.smooth_smul h s }
  N := cut0 i D
  N_mem := fun f h => smooth_congr hD h (fun _ hg => level_restriction_apply_on f hg)
  N_idem := fun f => (level_restriction_eq_iff _ _).2 (fun _ hg => level_restriction_apply_on f hg)

theorem good0 (hD : IsOpen D) {T : (Mx k r → E) → Mx k r → E} (h : Qx2.Good k r i D T) :
    (levData E i hD).Good T where
  mem := fun f hf => h.sm f hf
  congr := fun f _ f' _ he => (level_restriction_eq_iff _ _).2 (h.loc f f' ((level_restriction_eq_iff _ _).1 he))
  lin := fun f hf f' hf' s => by
    show cut0 i D _ = cut0 i D _ + s • cut0 i D _
    rw [← map_smul, ← map_add]
    exact (level_restriction_eq_iff _ _).2 (h.lin f f' s hf hf')

def E0 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin (r + 1)) {D : Set (Mx k r)} (hD : IsOpen D)
    (a b : Fin (mdim k r i)) : Module.End ℂ (levData E i hD).V :=
  (levData E i hD).hat (EH k r (posL k r i a) (posL k r i b))

theorem level_generator_good (hD : IsOpen D) (a b : Fin (mdim k r i)) :
    (levData E i hD).Good (EH k r (posL k r i a) (posL k r i b)) := good0 hD (Qx2.good_eh hD a b)

theorem level_generator_apply (hD : IsOpen D) (a b : Fin (mdim k r i)) (F : (levData E i hD).V) {g : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) :
    ((E0 E i hD a b F : (levData E i hD).V) : Mx k r → E) g = EH k r (posL k r i a) (posL k r i b) F g := by
  show (((levData E i hD).hat (EH k r (posL k r i a) (posL k r i b)) F : (levData E i hD).V) : Mx k r → E) g = _
  rw [HatData.hat_apply (level_generator_good hD a b)]
  exact level_restriction_apply_on _ hg

end Lev

theorem level_generators_gl_relations (hGl : EabGlLev) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin (r + 1))
    {D : Set (Mx k r)} (hD : IsOpen D) : GlRel (E0 E i hD) := by
  intro a b c d
  have g := fun a b => level_generator_good (E := E) (i := i) hD a b
  have e1 : (if b = c then E0 E i hD a d else 0) =
      (levData E i hD).hat (fun f => if b = c then EH k r (posL k r i a) (posL k r i d) f else 0) := by
    split_ifs
    · rfl
    · exact HatData.hat_zero.symm
  have e2 : (if d = a then E0 E i hD c b else 0) =
      (levData E i hD).hat (fun f => if d = a then EH k r (posL k r i c) (posL k r i b) f else 0) := by
    split_ifs
    · rfl
    · exact HatData.hat_zero.symm
  have g1 : (levData E i hD).Good (fun f => if b = c then EH k r (posL k r i a) (posL k r i d) f else 0) := by
    split_ifs
    · exact g a d
    · exact HatData.good_zero
  have g2 : (levData E i hD).Good (fun f => if d = a then EH k r (posL k r i c) (posL k r i b) f else 0) := by
    split_ifs
    · exact g c b
    · exact HatData.good_zero
  rw [e1, e2]
  unfold E0
  rw [← HatData.hat_comp (g a b) (g c d), ← HatData.hat_comp (g c d) (g a b),
    ← HatData.hat_sub ((g a b).comp (g c d)) ((g c d).comp (g a b)), ← HatData.hat_sub g1 g2]
  refine HatData.hat_congr (((g a b).comp (g c d)).sub ((g c d).comp (g a b))) (g1.sub g2) ?_
  intro f hf
  refine (level_restriction_eq_iff _ _).2 (fun x hx => ?_)
  have := hGl E k r i D a b c d f hD hf x hx
  simp only [Pi.sub_apply]
  rw [this]
  split_ifs <;> simp

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Ring
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem qminor_cast {t t' : ℕ} (h : t = t') (a b : Fin t' → Fin n) (u : ℂ) :
    qminor E (a ∘ Fin.cast h) (b ∘ Fin.cast h) u = qminor E a b u := by
  subst h
  rfl

theorem commute_qminor (X : A) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ)
    (h : ∀ i j w, Commute X (Tm E w (a i) (b j))) : Commute X (qminor E a b u) := by
  unfold qminor
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.mul_right (Int.cast_commute _ _).symm (Commute.list_prod_right _ _ ?_)
  intro x hx
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  exact h _ _ _

variable {E}

theorem commute_Tm_E (hE : GlRel E) (u : ℂ) {p c d : Fin n} (h1 : p ≠ c) (h2 : d ≠ p) :
    Commute (Tm E u p p) (E c d) := Tm_comm E hE u h1 h2

theorem commute_Tm_Tm (hE : GlRel E) (u w : ℂ) {p c d : Fin n} (h1 : p ≠ c) (h2 : d ≠ p) :
    Commute (Tm E u p p) (Tm E w c d) := by
  show Commute _ ((if c = d then algebraMap ℂ A w else 0) + E c d)
  refine Commute.add_right ?_ (commute_Tm_E hE u h1 h2)
  split_ifs
  · exact (Algebra.commutes w _).symm
  · exact Commute.zero_right _

theorem commute_Tm_qminor (hE : GlRel E) (u w : ℂ) {p : Fin n} {t : ℕ} {a b : Fin t → Fin n}
    (ha : ∀ i, a i ≠ p) (hb : ∀ j, b j ≠ p) : Commute (Tm E u p p) (qminor E a b w) :=
  commute_qminor E _ a b w (fun i j w' => commute_Tm_Tm hE u w' (ha i).symm (hb j))

end Ring

section Bridge
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem good_Top (hD : IsOpen D) (u : ℂ) (a b : Fin (mdim k r i)) :
    (levData E i hD).Good (QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b)) := good0 hD (Qx2.good_top hD u a b)

theorem quantum_tensor_level_generator (hD : IsOpen D) (u : ℂ) (a b : Fin (mdim k r i)) :
    Tm (E0 E i hD) u a b = (levData E i hD).hat (QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b)) := by
  by_cases h : a = b
  · subst h
    have e : (QuantumDeterminants.Top (E := E) (EH k r) u (posL k r i a) (posL k r i a)) =
        fun f => u • f + EH k r (posL k r i a) (posL k r i a) f := by
      funext f g
      simp [QuantumDeterminants.Top]
    rw [e, HatData.hat_add (HatData.good_id.smul u) (level_generator_good hD a a), HatData.hat_smul HatData.good_id,
      HatData.hat_id]
    simp [Tm, E0, Algebra.algebraMap_eq_smul_one]
  · have hp : posL k r i a ≠ posL k r i b := fun e => h (Qx2.posL_inj i e)
    have e : (QuantumDeterminants.Top (E := E) (EH k r) u (posL k r i a) (posL k r i b)) = EH k r (posL k r i a) (posL k r i b) := by
      funext f g
      simp [QuantumDeterminants.Top, hp]
    rw [e]
    simp [Tm, E0, h]

theorem good_qm (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    (levData E i hD).Good (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u) :=
  good0 hD (Qx2.good_qminor hD a b u)

theorem quantum_minor_level_eq_hat (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    qminor (E0 E i hD) a b u = (levData E i hD).hat (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u) := by
  have gL : ∀ σ : Equiv.Perm (Fin t), ∀ T ∈ (List.ofFn fun j : Fin t =>
      QuantumDeterminants.Top (E := E) (EH k r) (u - ((j : ℕ) : ℂ)) ((posL k r i ∘ a) (σ j)) ((posL k r i ∘ b) j)),
      (levData E i hD).Good T := by
    intro σ T hT
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact good_Top hD _ _ _
  have e : (qminorOp (E := E) (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u) =
      fun f => ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
        (List.ofFn fun j : Fin t => QuantumDeterminants.Top (E := E) (EH k r) (u - ((j : ℕ) : ℂ)) ((posL k r i ∘ a) (σ j))
          ((posL k r i ∘ b) j)).foldr (fun T h => T h) f) := rfl
  rw [e, HatData.hat_sum _ (fun σ _ => (HatData.good_foldr _ (gL σ)).smul _)]
  unfold qminor
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [HatData.hat_smul (HatData.good_foldr _ (gL σ)), HatData.hat_foldr _ (gL σ), List.map_ofFn,
    Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  congr 3
  funext j
  exact quantum_tensor_level_generator hD _ _ _

theorem quantum_minor_level_apply (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ)
    (F : (levData E i hD).V) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    ((qminor (E0 E i hD) a b u F : (levData E i hD).V) : Mx k r → E) g =
      qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u F g := by
  rw [quantum_minor_level_eq_hat, HatData.hat_apply (good_qm hD a b u)]
  exact level_restriction_apply_on _ hg

end Bridge

section Border
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} {E : Fin n → Fin n → A} {e es : Fin n} {v : Fin m → Fin n}

theorem borderE' (hB : BorderE) (hE : GlRel E) (hv : IsBorder e es v) (u : ℂ) :
    qminor E (bE e v) (bE e v) u = qminor E v v (u - 1) * Tm E u e e -
        ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
          (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * E e (v x)) := by
  rw [hB A n m E e es v hE hv u, (commute_Tm_qminor hE u (u - 1) hv.2.2.1 hv.2.2.1).eq]

theorem borderS' (hB : BorderS) (hE : GlRel E) (hv : IsBorder e es v) (u : ℂ) :
    qminor E (bS v es) (bS v es) u = Tm E (u - (m : ℂ)) es es * qminor E v v u -
        ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
          (E es (v x) * qminor E (v ∘ skip1 w) (v ∘ skip1 x) u * E (v w) es) := by
  rw [hB A n m E e es v hE hv u, (commute_Tm_qminor hE (u - (m : ℂ)) u hv.2.2.2 hv.2.2.2).eq]

end Border

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section SF
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}

def sfData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (L : Fin (r + 1))
    {Dc : (Fin r → ℂ) → Set (Mx k r)} (ho : IsOpen (UU Dc)) : HatData (Fn k r E) :=
  mkData L Dc (SmoothFam k r L (UU Dc)) Qx3.sf_zero (fun _ _ h h' => Qx3.sf_add h h')
    (fun s _ h => Qx3.sf_csmul s h)
    (fun Φ h => Qx3.sf_congr_on ho (fun _ hx => hx) (fun x hx hxG => cutP_on Φ hx.1 hxG hx.2) h)

theorem sf_ext (ho : IsOpen (UU Dc)) {Ψ Ψ' : (sfData E L ho).V}
    (h : ∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → (Ψ : Fn k r E) c g = (Ψ' : Fn k r E) c g) : Ψ = Ψ' := by
  apply Subtype.ext
  rw [← Ψ.2.2, ← Ψ'.2.2]
  exact (cutP_eq_iff _ _).2 h

theorem sf_hat_apply (ho : IsOpen (UU Dc)) {T : Fn k r E → Fn k r E} (hT : (sfData E L ho).Good T)
    (Ψ : (sfData E L ho).V) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r L) (hgD : g ∈ Dc c) :
    (((sfData E L ho).hat T Ψ : (sfData E L ho).V) : Fn k r E) c g = T Ψ c g := by
  rw [HatData.hat_apply hT]
  exact cutP_on _ hc hg hgD

theorem sf_good_of (ho : IsOpen (UU Dc)) {T : Fn k r E → Fn k r E}
    (h1 : ∀ Φ, SmoothFam k r L (UU Dc) Φ → SmoothFam k r L (UU Dc) (T Φ))
    (h2 : ∀ Φ Ψ, SmoothFam k r L (UU Dc) Φ → SmoothFam k r L (UU Dc) Ψ →
      (∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → Φ c g = Ψ c g) →
      ∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → T Φ c g = T Ψ c g)
    (h3 : ∀ Φ Ψ, SmoothFam k r L (UU Dc) Φ → SmoothFam k r L (UU Dc) Ψ → ∀ s : ℂ,
      ∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → T (Φ + s • Ψ) c g = T Φ c g + s • T Ψ c g) :
    (sfData E L ho).Good T where
  mem := h1
  congr := fun Φ h Ψ h' he => (cutP_eq_iff _ _).2 (h2 Φ Ψ h h' ((cutP_eq_iff _ _).1 he))
  lin := fun Φ h Ψ h' s => by
    show cutP L Dc _ = cutP L Dc _ + s • cutP L Dc _
    rw [← map_smul, ← map_add]
    exact (cutP_eq_iff _ _).2 (h3 Φ Ψ h h' s)

theorem sf_diff {Φ : Fn k r E} (h : SmoothFam k r L (UU Dc) Φ) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hg : g ∈ Glev k r L) (hgD : g ∈ Dc c) : DifferentiableAt ℝ (fun c' => Φ c' g) c :=
  Qx3.fam_differentiableAt h (x := (c, g)) ⟨hc, hgD⟩ hg

theorem sf_good_crd (ho : IsOpen (UU Dc)) (a : Fin r) (q : Fin 6) : (sfData E L ho).Good (crd (opL a q)) :=
  sf_good_of ho (fun _ h => Qx3.sf_opL (fun _ hx => hx.1) a q h)
    (fun Φ Ψ _ _ he c hc g hg hgD => by
      apply opL_germ
      filter_upwards [near_pt ho hc hgD] with c' hc'
      exact he c' hc'.1 g hg hc'.2)
    (fun _ _ h h' s _ hc _ hg hgD => opL_lin a q s (sf_diff h hc hg hgD) (sf_diff h' hc hg hgD))

theorem open_slice (ho : IsOpen (UU Dc)) {c : Fin r → ℂ} (hc : c ∈ OmX r) : IsOpen (Dc c) := by
  have hcont : Continuous (fun g : Mx k r => ((c, g) : XX k r)) := continuous_const.prodMk continuous_id
  have := ho.preimage hcont
  convert this using 1
  ext g
  exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩

theorem sf_good_grp (ho : IsOpen (UU Dc)) {T : (Mx k r → E) → Mx k r → E} (hP : Qx3.Pres L (UU Dc) T)
    (hLL : ∀ c ∈ OmX r, Qx2.LL k r L (Dc c) T) : (sfData E L ho).Good (grp T) :=
  sf_good_of ho (fun Φ h => hP Φ h)
    (fun Φ Ψ _ _ he c hc g hg hgD => (hLL c hc).loc (Φ c) (Ψ c) (fun x hx => he c hc x hx.1 hx.2) g ⟨hg, hgD⟩)
    (fun Φ Ψ h h' s c hc g hg hgD =>
      (hLL c hc).lin (Φ c) (Ψ c) s (Qx3.sf_slice h hc) (Qx3.sf_slice h' hc) g ⟨hg, hgD⟩)

def mulF (a : Fn k r ℂ) (Φ : Fn k r E) : Fn k r E := fun c g => a c g • Φ c g

theorem sf_good_mul (ho : IsOpen (UU Dc)) {a : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a) :
    (sfData E L ho).Good (mulF a) :=
  sf_good_of ho (fun _ h => Qx3.sf_smul ha h)
    (fun Φ Ψ _ _ he c hc g hg hgD => by
      show a c g • Φ c g = a c g • Ψ c g
      rw [he c hc g hg hgD])
    (fun Φ Ψ _ _ s c _ g _ _ => by
      show a c g • (Φ c g + s • Ψ c g) = a c g • Φ c g + s • (a c g • Ψ c g)
      rw [smul_add, smul_comm])

def mulB (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (L : Fin (r + 1)) {Dc : (Fin r → ℂ) → Set (Mx k r)}
    (ho : IsOpen (UU Dc)) (a : Fn k r ℂ) : Module.End ℂ (sfData E L ho).V := (sfData E L ho).hat (mulF a)

theorem mulB_congr (ho : IsOpen (UU Dc)) {a a' : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a)
    (ha' : SmoothFam k r L (UU Dc) a') (h : ∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → a c g = a' c g) :
    mulB E L ho a = mulB E L ho a' := by
  show (sfData E L ho).hat (mulF a) = (sfData E L ho).hat (mulF a')
  apply HatData.hat_congr (sf_good_mul ho ha) (sf_good_mul ho ha')
  intro x _
  show cutP L Dc (mulF a x) = cutP L Dc (mulF a' x)
  apply (cutP_eq_iff _ _).2
  intro c hc g hg hgD
  show a c g • x c g = a' c g • x c g
  rw [h c hc g hg hgD]

theorem mulB_mul (ho : IsOpen (UU Dc)) {a a' : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a)
    (ha' : SmoothFam k r L (UU Dc) a') :
    mulB E L ho a * mulB E L ho a' = mulB E L ho (fun c g => a c g * a' c g) := by
  show (sfData E L ho).hat (mulF a) * (sfData E L ho).hat (mulF a') =
    (sfData E L ho).hat (mulF (fun c g => a c g * a' c g))
  rw [← HatData.hat_comp (sf_good_mul ho ha) (sf_good_mul ho ha')]
  congr 1
  funext Φ c g
  simp only [mulF, smul_smul]

theorem mulB_comm (ho : IsOpen (UU Dc)) {a a' : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a)
    (ha' : SmoothFam k r L (UU Dc) a') : Commute (mulB E L ho a) (mulB E L ho a') := by
  show mulB E L ho a * mulB E L ho a' = mulB E L ho a' * mulB E L ho a
  rw [mulB_mul ho ha ha', mulB_mul ho ha' ha]
  congr 1
  funext c g
  exact mul_comm _ _

theorem mulB_smul (ho : IsOpen (UU Dc)) {a : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a) (s : ℂ) :
    mulB E L ho (fun c g => s * a c g) = s • mulB E L ho a := by
  show (sfData E L ho).hat (mulF (fun c g => s * a c g)) = s • (sfData E L ho).hat (mulF a)
  rw [← HatData.hat_smul (sf_good_mul ho ha) s]
  congr 1
  funext Φ c g
  simp only [mulF, Pi.smul_apply, mul_smul]

theorem mulB_zero (ho : IsOpen (UU Dc)) : mulB E L ho (fun _ _ => 0) = 0 := by
  show (sfData E L ho).hat (mulF (fun _ _ => 0)) = 0
  rw [← HatData.hat_zero (H := sfData E L ho)]
  congr 1
  funext Φ c g
  simp [mulF]

theorem mulB_grp_comm (ho : IsOpen (UU Dc)) {α : (Fin r → ℂ) → ℂ} (hα : SmoothFam k r L (UU Dc) (fun c _ => α c))
    {T : (Mx k r → E) → Mx k r → E} (hP : Qx3.Pres L (UU Dc) T) (hLL : ∀ c ∈ OmX r, Qx2.LL k r L (Dc c) T) :
    Commute (mulB E L ho (fun c _ => α c)) ((sfData E L ho).hat (grp T)) := by
  show _ * _ = _ * _
  unfold mulB
  have g1 := sf_good_mul (E := E) ho hα
  have g2 := sf_good_grp ho hP hLL
  rw [← HatData.hat_comp g1 g2, ← HatData.hat_comp g2 g1]
  refine HatData.hat_congr (g1.comp g2) (g2.comp g1) (fun Φ hΦ => (cutP_eq_iff _ _).2 (fun c hc g hg hgD => ?_))
  show α c • T (Φ c) g = T (fun x => α c • Φ c x) g
  have hs := Qx3.sf_slice (Dc := Dc) hΦ hc
  have h0 := (hLL c hc).lin (fun _ => 0) (Φ c) (α c) Qx2.smooth_zero hs g ⟨hg, hgD⟩
  have h00 := (hLL c hc).lin (fun _ => 0) (fun _ => 0) 1 Qx2.smooth_zero Qx2.smooth_zero g ⟨hg, hgD⟩
  simp only [smul_zero, add_zero, one_smul, left_eq_add] at h00
  simp only [zero_add, h00] at h0
  exact h0.symm

end SF

section Prod
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem pOp_smul (l : Fin r) {a : (Fin r → ℂ) → ℂ} {f : (Fin r → ℂ) → E} {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (ha : DifferentiableAt ℝ a c) (hf : DifferentiableAt ℝ f c) :
    pOp l (fun x => a x • f x) c = a c • pOp l f c + pOp l a c • f c := by
  unfold pOp
  rw [if_pos hc, if_pos hc, if_pos hc, WirtingerDerivatives.wirt_eq, WirtingerDerivatives.wirt_eq, WirtingerDerivatives.wirt_eq,
    WirtingerDerivatives.Wc_smul ha hf, smul_add, smul_smul, smul_smul, smul_smul, smul_eq_mul, mul_comm (c l) (a c), add_comm]

theorem pbOp_smul (l : Fin r) {a : (Fin r → ℂ) → ℂ} {f : (Fin r → ℂ) → E} {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (ha : DifferentiableAt ℝ a c) (hf : DifferentiableAt ℝ f c) :
    pbOp l (fun x => a x • f x) c = a c • pbOp l f c + pbOp l a c • f c := by
  unfold pbOp
  rw [if_pos hc, if_pos hc, if_pos hc, WirtingerDerivatives.wirtBar_eq, WirtingerDerivatives.wirtBar_eq, WirtingerDerivatives.wirtBar_eq,
    WirtingerDerivatives.Wc_smul ha hf, smul_add, smul_smul, smul_smul, smul_smul, smul_eq_mul, mul_comm (star (c l)) (a c),
    add_comm]

end Prod

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Vals

theorem pOp_coord (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) : pOp l (fun x : Fin r → ℂ => x l) c = c l := by
  have hd : fderiv ℝ (fun x : Fin r → ℂ => x l) c = ContinuousLinearMap.proj l :=
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin r => ℂ) l c).fderiv
  simp only [pOp, wirt, hc, if_true, hd, ContinuousLinearMap.proj_apply, Pi.single_eq_same, smul_eq_mul,
    Complex.I_mul_I]
  ring

theorem pOp_coordBar (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    pOp l (fun x : Fin r → ℂ => star (x l)) c = 0 := by
  have hd : fderiv ℝ (fun x : Fin r → ℂ => star (x l)) c =
      (Complex.conjCLE.toContinuousLinearMap).comp (ContinuousLinearMap.proj l) :=
    (Complex.conjCLE.hasFDerivAt.comp c (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin r => ℂ) l c)).fderiv
  simp only [pOp, wirt, hc, if_true, hd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I,
    smul_eq_mul, mul_neg, Complex.I_mul_I]
  ring

theorem pOp_cbi (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    pOp l (fun x : Fin r → ℂ => (star (x l))⁻¹) c = 0 := by
  have := WirtingerDerivatives.wirt_coef hc l (k := l) 5
  unfold pOp
  rw [if_pos hc]
  change wirt l (fun y : Fin r → ℂ => (star (y l))⁻¹) c = _ at this
  rw [this]
  simp

theorem pbOp_coord (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) : pbOp l (fun x : Fin r → ℂ => x l) c = 0 := by
  have hd : fderiv ℝ (fun x : Fin r → ℂ => x l) c = ContinuousLinearMap.proj l :=
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin r => ℂ) l c).fderiv
  simp only [pbOp, wirtBar, hc, if_true, hd, ContinuousLinearMap.proj_apply, Pi.single_eq_same, smul_eq_mul,
    Complex.I_mul_I]
  ring

theorem pbOp_coordBar (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    pbOp l (fun x : Fin r → ℂ => star (x l)) c = star (c l) := by
  have hd : fderiv ℝ (fun x : Fin r → ℂ => star (x l)) c =
      (Complex.conjCLE.toContinuousLinearMap).comp (ContinuousLinearMap.proj l) :=
    (Complex.conjCLE.hasFDerivAt.comp c (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin r => ℂ) l c)).fderiv
  simp only [pbOp, wirtBar, hc, if_true, hd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I,
    smul_eq_mul, mul_neg, Complex.I_mul_I]
  ring

theorem pOp_const (l : Fin r) (s : ℂ) (c : Fin r → ℂ) : pOp l (fun _ : Fin r → ℂ => s) c = 0 := by
  simp [pOp, wirt]

theorem pbOp_const (l : Fin r) (s : ℂ) (c : Fin r → ℂ) : pbOp l (fun _ : Fin r → ℂ => s) c = 0 := by
  simp [pbOp, wirtBar]

theorem diff_gamma (l : Fin r) (n : ℕ) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    DifferentiableAt ℝ (fun x : Fin r → ℂ => ((‖x l‖ ^ n : ℝ) : ℂ)) c := by
  have h1 : DifferentiableAt ℝ (fun x : Fin r → ℂ => ‖x l‖ ^ n) c :=
    ((show DifferentiableAt ℝ (fun x : Fin r → ℂ => x l) c by fun_prop).norm ℝ
      ((show ∀ l, c l ≠ 0 from hc) l)).pow n
  exact Complex.ofRealCLM.differentiableAt.comp c h1

theorem nu_sq (l : Fin r) : (fun x : Fin r → ℂ => ((‖x l‖ ^ 1 : ℝ) : ℂ) • ((‖x l‖ ^ 1 : ℝ) : ℂ)) =
    fun x => x l • star (x l) := by
  funext x
  simp only [pow_one, smul_eq_mul, Complex.star_def]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem nu_ne (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) : ((‖c l‖ ^ 1 : ℝ) : ℂ) ≠ 0 := by
  rw [pow_one, Complex.ofReal_ne_zero, norm_ne_zero_iff]
  exact (show ∀ l, c l ≠ 0 from hc) l

theorem diff_coord (l : Fin r) (c : Fin r → ℂ) : DifferentiableAt ℝ (fun x : Fin r → ℂ => x l) c := by
  fun_prop

theorem diff_coordBar (l : Fin r) (c : Fin r → ℂ) : DifferentiableAt ℝ (fun x : Fin r → ℂ => star (x l)) c := by
  have h := Complex.conjCLE.differentiableAt (x := c l)
  exact h.comp c (diff_coord l c)

theorem pOp_nu (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    pOp l (fun x : Fin r → ℂ => ((‖x l‖ ^ 1 : ℝ) : ℂ)) c = (1 / 2 : ℂ) * ((‖c l‖ ^ 1 : ℝ) : ℂ) := by
  have h1 := pOp_smul l hc (diff_gamma l 1 hc) (diff_gamma l 1 hc)
  have h2 := pOp_smul l hc (diff_coord l c) (diff_coordBar l c)
  rw [nu_sq, h2, pOp_coord l hc, pOp_coordBar l hc] at h1
  have h3 := congrFun (nu_sq l) c
  simp only [smul_eq_mul, mul_zero, zero_add] at h1 h3
  have hne := nu_ne l hc
  rw [← h3] at h1
  apply mul_left_cancel₀ hne
  linear_combination (-1 / 2 : ℂ) * h1

theorem pbOp_nu (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    pbOp l (fun x : Fin r → ℂ => ((‖x l‖ ^ 1 : ℝ) : ℂ)) c = (1 / 2 : ℂ) * ((‖c l‖ ^ 1 : ℝ) : ℂ) := by
  have h1 := pbOp_smul l hc (diff_gamma l 1 hc) (diff_gamma l 1 hc)
  have h2 := pbOp_smul l hc (diff_coord l c) (diff_coordBar l c)
  rw [nu_sq, h2, pbOp_coord l hc, pbOp_coordBar l hc] at h1
  have h3 := congrFun (nu_sq l) c
  simp only [smul_eq_mul, zero_mul, add_zero] at h1 h3
  have hne := nu_ne l hc
  rw [← h3] at h1
  apply mul_left_cancel₀ hne
  linear_combination (-1 / 2 : ℂ) * h1

theorem gamma_succ (l : Fin r) (n : ℕ) : (fun x : Fin r → ℂ => ((‖x l‖ ^ (n + 1) : ℝ) : ℂ)) =
    fun x => ((‖x l‖ ^ n : ℝ) : ℂ) • ((‖x l‖ ^ 1 : ℝ) : ℂ) := by
  funext x
  rw [smul_eq_mul, ← Complex.ofReal_mul, ← pow_add]

theorem pOp_gamma (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) : ∀ n : ℕ,
    pOp l (fun x : Fin r → ℂ => ((‖x l‖ ^ n : ℝ) : ℂ)) c = ((n : ℂ) / 2) * ((‖c l‖ ^ n : ℝ) : ℂ)
  | 0 => by simpa using pOp_const l 1 c
  | n + 1 => by
    rw [gamma_succ, pOp_smul l hc (diff_gamma l n hc) (diff_gamma l 1 hc), pOp_nu l hc, pOp_gamma l hc n]
    simp only [smul_eq_mul]
    push_cast
    ring

theorem pbOp_gamma (l : Fin r) {c : Fin r → ℂ} (hc : c ∈ OmX r) : ∀ n : ℕ,
    pbOp l (fun x : Fin r → ℂ => ((‖x l‖ ^ n : ℝ) : ℂ)) c = ((n : ℂ) / 2) * ((‖c l‖ ^ n : ℝ) : ℂ)
  | 0 => by simpa using pbOp_const l 1 c
  | n + 1 => by
    rw [gamma_succ, pbOp_smul l hc (diff_gamma l n hc) (diff_gamma l 1 hc), pbOp_nu l hc, pbOp_gamma l hc n]
    simp only [smul_eq_mul]
    push_cast
    ring

end Vals

section PB
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}

def opB (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (L : Fin (r + 1)) {Dc : (Fin r → ℂ) → Set (Mx k r)}
    (ho : IsOpen (UU Dc)) (l : Fin r) (q : Fin 6) : Module.End ℂ (sfData E L ho).V :=
  (sfData E L ho).hat (crd (opL l q))

theorem P_mulB (ho : IsOpen (UU Dc)) (l : Fin r) {a : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a) :
    opB E L ho l 0 * mulB E L ho a = mulB E L ho a * opB E L ho l 0 + mulB E L ho (crd (opL l 0) a) := by
  have ha' : SmoothFam k r L (UU Dc) (crd (opL l 0) a) := Qx3.sf_opL (fun _ hx => hx.1) l 0 ha
  have g1 := sf_good_crd (E := E) (L := L) ho l 0
  have g2 := sf_good_mul (E := E) ho ha
  have g3 := sf_good_mul (E := E) ho ha'
  unfold opB mulB
  rw [← HatData.hat_comp g1 g2, ← HatData.hat_comp g2 g1, ← HatData.hat_add (g2.comp g1) g3]
  refine HatData.hat_congr (g1.comp g2) ((g2.comp g1).add g3) (fun Φ hΦ => (cutP_eq_iff _ _).2
    (fun c hc g hg hgD => ?_))
  exact pOp_smul l hc (sf_diff ha hc hg hgD) (sf_diff hΦ hc hg hgD)

theorem Pb_mulB (ho : IsOpen (UU Dc)) (l : Fin r) {a : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a) :
    opB E L ho l 3 * mulB E L ho a = mulB E L ho a * opB E L ho l 3 + mulB E L ho (crd (opL l 3) a) := by
  have ha' : SmoothFam k r L (UU Dc) (crd (opL l 3) a) := Qx3.sf_opL (fun _ hx => hx.1) l 3 ha
  have g1 := sf_good_crd (E := E) (L := L) ho l 3
  have g2 := sf_good_mul (E := E) ho ha
  have g3 := sf_good_mul (E := E) ho ha'
  unfold opB mulB
  rw [← HatData.hat_comp g1 g2, ← HatData.hat_comp g2 g1, ← HatData.hat_add (g2.comp g1) g3]
  refine HatData.hat_congr (g1.comp g2) ((g2.comp g1).add g3) (fun Φ hΦ => (cutP_eq_iff _ _).2
    (fun c hc g hg hgD => ?_))
  exact pbOp_smul l hc (sf_diff ha hc hg hgD) (sf_diff hΦ hc hg hgD)

theorem P_mulB_of (ho : IsOpen (UU Dc)) (l : Fin r) {a : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a) (s : ℂ)
    (h : ∀ c ∈ OmX r, ∀ g, pOp l (fun c' => a c' g) c = s * a c g) :
    opB E L ho l 0 * mulB E L ho a = mulB E L ho a * (opB E L ho l 0 + s • 1) := by
  rw [P_mulB ho l ha, mulB_congr ho (Qx3.sf_opL (fun _ hx => hx.1) l 0 ha) (Qx3.sf_csmul s ha)
    (fun c hc g _ _ => h c hc g)]
  have : mulB E L ho (fun c g => s • a c g) = s • mulB E L ho a := mulB_smul ho ha s
  rw [this, mul_add, mul_smul_comm, mul_one]

theorem Pb_mulB_of (ho : IsOpen (UU Dc)) (l : Fin r) {a : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a) (s : ℂ)
    (h : ∀ c ∈ OmX r, ∀ g, pbOp l (fun c' => a c' g) c = s * a c g) :
    opB E L ho l 3 * mulB E L ho a = mulB E L ho a * (opB E L ho l 3 + s • 1) := by
  rw [Pb_mulB ho l ha, mulB_congr ho (Qx3.sf_opL (fun _ hx => hx.1) l 3 ha) (Qx3.sf_csmul s ha)
    (fun c hc g _ _ => h c hc g)]
  have : mulB E L ho (fun c g => s • a c g) = s • mulB E L ho a := mulB_smul ho ha s
  rw [this, mul_add, mul_smul_comm, mul_one]

end PB

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section IntGen
variable {V₀ V₁ : Type*} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  (ρ : V₀ →ₗ[ℂ] V₁) (VL : Submodule ℂ V₀)

def IntQ (T : Module.End ℂ V₀) (T' : Module.End ℂ V₁) : Prop :=
  (∀ F ∈ VL, T F ∈ VL) ∧ ∀ F ∈ VL, ρ (T F) = T' (ρ F)

variable {ρ VL}

theorem IntQ.mul {T S : Module.End ℂ V₀} {T' S' : Module.End ℂ V₁} (h : IntQ ρ VL T T') (h' : IntQ ρ VL S S') :
    IntQ ρ VL (T * S) (T' * S') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine And.intro (fun F hF => h1 _ (h1' F hF)) (fun F hF => ?_)
  show ρ (T (S F)) = T' (S' (ρ F))
  rw [h2 _ (h1' F hF), h2' F hF]

theorem IntQ.add {T S : Module.End ℂ V₀} {T' S' : Module.End ℂ V₁} (h : IntQ ρ VL T T') (h' : IntQ ρ VL S S') :
    IntQ ρ VL (T + S) (T' + S') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine And.intro (fun F hF => VL.add_mem (h1 F hF) (h1' F hF)) (fun F hF => ?_)
  show ρ (T F + S F) = T' (ρ F) + S' (ρ F)
  rw [map_add, h2 F hF, h2' F hF]

theorem IntQ.smul {T : Module.End ℂ V₀} {T' : Module.End ℂ V₁} (h : IntQ ρ VL T T') (s : ℂ) :
    IntQ ρ VL (s • T) (s • T') := by
  obtain ⟨h1, h2⟩ := h
  refine And.intro (fun F hF => VL.smul_mem s (h1 F hF)) (fun F hF => ?_)
  show ρ (s • T F) = s • T' (ρ F)
  rw [map_smul, h2 F hF]

theorem IntQ.neg {T : Module.End ℂ V₀} {T' : Module.End ℂ V₁} (h : IntQ ρ VL T T') : IntQ ρ VL (-T) (-T') := by
  obtain ⟨h1, h2⟩ := h
  refine And.intro (fun F hF => VL.neg_mem (h1 F hF)) (fun F hF => ?_)
  show ρ (-T F) = -T' (ρ F)
  rw [map_neg, h2 F hF]

theorem IntQ.sub {T S : Module.End ℂ V₀} {T' S' : Module.End ℂ V₁} (h : IntQ ρ VL T T') (h' : IntQ ρ VL S S') :
    IntQ ρ VL (T - S) (T' - S') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine And.intro (fun F hF => VL.sub_mem (h1 F hF) (h1' F hF)) (fun F hF => ?_)
  show ρ (T F - S F) = T' (ρ F) - S' (ρ F)
  rw [map_sub, h2 F hF, h2' F hF]

theorem int_one : IntQ ρ VL 1 1 := by
  refine And.intro (fun F hF => hF) (fun F _ => ?_)
  rfl

theorem int_zero : IntQ ρ VL 0 0 := by
  refine And.intro (fun F _ => VL.zero_mem) (fun F _ => ?_)
  show ρ 0 = 0
  exact map_zero ρ

theorem int_algebraMap (s : ℂ) : IntQ ρ VL (algebraMap ℂ _ s) (algebraMap ℂ _ s) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact IntQ.smul int_one s

theorem int_intCast (n : ℤ) : IntQ ρ VL (n : Module.End ℂ V₀) (n : Module.End ℂ V₁) := by
  rw [← map_intCast (algebraMap ℂ (Module.End ℂ V₀)) n, ← map_intCast (algebraMap ℂ (Module.End ℂ V₁)) n]
  exact int_algebraMap _

theorem IntQ.sum {ι : Type*} (s : Finset ι) {T : ι → Module.End ℂ V₀} {T' : ι → Module.End ℂ V₁}
    (h : ∀ j ∈ s, IntQ ρ VL (T j) (T' j)) : IntQ ρ VL (∑ j ∈ s, T j) (∑ j ∈ s, T' j) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact int_zero
  · intro j s hj ih h
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end IntGen

section Idx
variable (k) {r : ℕ} (l : Fin r)

theorem mdim_eq : mdim k r l.castSucc = mdim k r l.succ + 1 + 1 := by
  have := l.isLt
  simp only [mdim, Fin.coe_castSucc, Fin.val_succ]
  omega

def e0 : Fin (mdim k r l.castSucc) := ⟨0, by rw [mdim_eq]; omega⟩
def es0 : Fin (mdim k r l.castSucc) := ⟨mdim k r l.succ + 1, by rw [mdim_eq]; omega⟩
def v0 (j : Fin (mdim k r l.succ)) : Fin (mdim k r l.castSucc) := ⟨j.val + 1, by rw [mdim_eq]; omega⟩

theorem level_position_first_basis : posL k r l.castSucc (e0 k l) = eI k r l := by
  apply Fin.ext
  simp [posL, e0, eI]

theorem level_position_last_basis : posL k r l.castSucc (es0 k l) = esI k r l := by
  apply Fin.ext
  have := l.isLt
  simp only [posL, es0, esI, mdim, Fin.coe_castSucc, Fin.val_succ]
  omega

theorem level_position_inclusion (j : Fin (mdim k r l.succ)) : posL k r l.castSucc (v0 k l j) = posL k r l.succ j := by
  apply Fin.ext
  simp only [posL, v0, Fin.coe_castSucc, Fin.val_succ]
  omega

theorem level_position_comp_inclusion : posL k r l.castSucc ∘ v0 k l = posL k r l.succ := by
  funext j
  exact level_position_inclusion k l j

theorem isBorder0 : IsBorder (e0 k l) (es0 k l) (v0 k l) := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro a b h
    have h' := congrArg Fin.val h
    simp only [v0] at h'
    exact Fin.ext (by omega)
  · intro h
    have h' := congrArg Fin.val h
    (simp only [e0, es0] at h') <;> omega
  · intro j h
    have h' := congrArg Fin.val h
    (simp only [v0, e0] at h') <;> omega
  · intro j h
    have h' := congrArg Fin.val h
    have hj := j.isLt
    (simp only [v0, es0] at h') <;> omega

theorem val_bS (y : Fin (mdim k r l.succ + 1)) : (bS (v0 k l) (es0 k l) y).val = y.val + 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) y
  · simp [bS, es0]
  · simp [bS, v0]

theorem val_bE (y : Fin (mdim k r l.succ + 1)) : (bE (e0 k l) (v0 k l) y).val = y.val := by
  refine Fin.cases ?_ (fun j => ?_) y
  · simp [bE, e0]
  · simp [bE, v0]

theorem val_bEbS (y : Fin (mdim k r l.succ + 1 + 1)) : (bE (e0 k l) (bS (v0 k l) (es0 k l)) y).val = y.val := by
  refine Fin.cases ?_ (fun j => ?_) y
  · simp [bE, e0]
  · simp only [bE, Fin.cons_succ, Fin.val_succ]
    exact val_bS k l j

theorem id_eq_b : (id : Fin (mdim k r l.castSucc) → Fin (mdim k r l.castSucc)) =
    bE (e0 k l) (bS (v0 k l) (es0 k l)) ∘ Fin.cast (mdim_eq k l) := by
  funext y
  apply Fin.ext
  rw [id_eq, Function.comp_apply, val_bEbS, Fin.coe_cast]

theorem skip_first_basis_eq_embedding : skip1 (e0 k l) = bS (v0 k l) (es0 k l) ∘ Fin.cast (by rw [mdim_eq]; rfl) := by
  funext j
  apply Fin.ext
  rw [Function.comp_apply, val_bS, Fin.coe_cast]
  have hn : ¬ (j.val < (e0 k l).val) := by
    show ¬ (j.val < 0)
    omega
  simp only [skip1, if_neg hn]

theorem skip_last_basis_eq_embedding : skip1 (es0 k l) = bE (e0 k l) (v0 k l) ∘ Fin.cast (by rw [mdim_eq]; rfl) := by
  funext j
  apply Fin.ext
  rw [Function.comp_apply, val_bE, Fin.coe_cast]
  have hj : j.val < mdim k r l.succ + 1 := by
    have h1 := j.isLt
    have h2 := mdim_eq k l
    omega
  have hlt : j.val < (es0 k l).val := by
    show j.val < mdim k r l.succ + 1
    exact hj
  simp only [skip1, if_pos hlt]

theorem double_skip_first_last_basis : skip2 (e0 k l) (es0 k l) = v0 k l ∘ Fin.cast (by rw [mdim_eq]; rfl) := by
  funext j
  apply Fin.ext
  have hj : j.val < mdim k r l.succ := by
    have h1 := j.isLt
    have h2 := mdim_eq k l
    omega
  have hn : ¬ (j.val < (e0 k l).val) := by
    show ¬ (j.val < 0)
    omega
  have hlt : j.val + 1 < (es0 k l).val := by
    show j.val + 1 < mdim k r l.succ + 1
    omega
  simp only [Function.comp_apply, skip2, if_neg hn, if_pos hlt, v0, Fin.coe_cast]

end Idx

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Rho
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem lev_ext {i : Fin (r + 1)} {D : Set (Mx k r)} (hD : IsOpen D) {F F' : (levData E i hD).V}
    (h : ∀ g ∈ Glev k r i ∩ D, (F : Mx k r → E) g = (F' : Mx k r → E) g) : F = F' := by
  apply Subtype.ext
  rw [← F.2.2, ← F'.2.2]
  exact (level_restriction_eq_iff _ _).2 h

theorem sf_const_fam {i : Fin (r + 1)} {D : Set (Mx k r)} {f : Mx k r → E} (h : SmoothLev k r i D f) :
    SmoothFam k r i (UU fun _ => D) (fun _ => f) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hf⟩ := h x₀.2 ⟨hg₀, hx₀.2⟩
  exact ⟨{x : XX k r | x.2 ∈ U}, fun x => F x.2, hU.preimage continuous_snd, hgU,
    hF.comp contDiff_snd.contDiffOn (fun _ hx => hx), fun x hx hxG => hf x.2 hx hxG⟩

def Dc1 (l : Fin r) (D : Set (Mx k r)) : (Fin r → ℂ) → Set (Mx k r) := stepD l (fun _ => D)

theorem ho1 (l : Fin r) {D : Set (Mx k r)} (hD : IsOpen D) : IsOpen (UU (Dc1 l D)) := open_step l (open_const hD)

def rr (l : Fin r) (F : Mx k r → E) : Fn k r E := fun c x => F (w1 k r l (c l) * x)

theorem sf_rr (hW : WeylLevelElementFacts) (l : Fin r) {D : Set (Mx k r)} {F : Mx k r → E} (h : SmoothLev k r l.castSucc D F) :
    SmoothFam k r l.succ (UU (Dc1 l D)) (rr l F) :=
  smooth_family_restriction hW l (sf_const_fam h) (fun _ hx => ⟨hx.1, hx.1, hx.2⟩)

def rho (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (hW : WeylLevelElementFacts) (l : Fin r) {D : Set (Mx k r)}
    (hD : IsOpen D) : (levData E l.castSucc hD).V →ₗ[ℂ] (sfData E l.succ (ho1 l hD)).V where
  toFun := fun F => (sfData E l.succ (ho1 l hD)).toV (rr l F) (sf_rr hW l F.2.1)
  map_add' := fun F F' => Subtype.ext (by
    show cutP _ _ (rr l ((F : Mx k r → E) + (F' : Mx k r → E))) = cutP _ _ _ + cutP _ _ _
    rw [← map_add]
    rfl)
  map_smul' := fun s F => Subtype.ext (by
    show cutP _ _ (rr l (s • (F : Mx k r → E))) = s • cutP _ _ _
    rw [← map_smul]
    rfl)

theorem rho_apply (hW : WeylLevelElementFacts) (l : Fin r) {D : Set (Mx k r)} (hD : IsOpen D) (F : (levData E l.castSucc hD).V)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {x : Mx k r} (hx : x ∈ Glev k r l.succ) (hxD : x ∈ Dc1 l D c) :
    ((rho E hW l hD F : (sfData E l.succ (ho1 l hD)).V) : Fn k r E) c x = (F : Mx k r → E) (w1 k r l (c l) * x) :=
  cutP_on _ hc hx hxD

theorem pt_mem (hW : WeylLevelElementFacts) (l : Fin r) {D : Set (Mx k r)} {c : Fin r → ℂ} (hc : c ∈ OmX r) {x : Mx k r}
    (hx : x ∈ Glev k r l.succ) (hxD : x ∈ Dc1 l D c) : w1 k r l (c l) * x ∈ Glev k r l.castSucc ∩ D :=
  ⟨mul_mem_of_mem_inv_mul_ideal hW l (hc l) hx, hxD⟩

def VLeft (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) {D : Set (Mx k r)} (hD : IsOpen D) :
    Submodule ℂ (levData E i hD).V where
  carrier := {F | LeftEq k r z i D (F : Mx k r → E)}
  zero_mem' := fun _ _ _ _ => by simp
  add_mem' := fun {F F'} h h' g hg n hn => by
    show (F : Mx k r → E) (n * g) + (F' : Mx k r → E) (n * g) = _ • ((F : Mx k r → E) g + (F' : Mx k r → E) g)
    rw [h g hg n hn, h' g hg n hn, smul_add]
  smul_mem' := fun s F h g hg n hn => by
    show s • (F : Mx k r → E) (n * g) = _ • (s • (F : Mx k r → E) g)
    rw [h g hg n hn, smul_comm]

def keepAlg {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {T | ∀ F ∈ W, T F ∈ W}
  mul_mem' := fun h h' F hF => h _ (h' F hF)
  add_mem' := fun h h' F hF => W.add_mem (h F hF) (h' F hF)
  algebraMap_mem' := fun s F hF => by
    rw [Module.algebraMap_end_apply]
    exact W.smul_mem s hF

theorem keep_qminor {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) {n t : ℕ}
    (E' : Fin n → Fin n → Module.End ℂ V) (h : ∀ a b, E' a b ∈ keepAlg W) (a b : Fin t → Fin n) (u : ℂ) :
    qminor E' a b u ∈ keepAlg W := by
  unfold qminor
  refine Subalgebra.sum_mem _ (fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _)
    (Subalgebra.list_prod_mem _ ?_))
  intro x hx
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  unfold Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

end Rho

section Keep
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem level_generator_preserves_left_space (hEP : EabPres) {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {D : Set (Mx k r)}
    (hD : IsDom k r z z' i D) (a b : Fin (mdim k r i)) : E0 E i hD.1 a b ∈ keepAlg (VLeft z i hD.1) := by
  intro F hF g hg n hn
  have h1 := ((hEP E k r z i D a b F F 0 hD.1 F.2.1 F.2.1).2.1 (fun g hg n hn => (dom_left hD hg hn).2) hF) g hg n hn
  rw [level_generator_apply hD.1 a b F hg, level_generator_apply hD.1 a b F (dom_left hD hg hn)]
  exact h1

end Keep

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Mult
variable {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}

def aC (k : ℕ) {r : ℕ} (l : Fin r) : Fn k r ℂ := fun c _ => c l
def aCi (k : ℕ) {r : ℕ} (l : Fin r) : Fn k r ℂ := fun c _ => (c l)⁻¹
def aCb (k : ℕ) {r : ℕ} (l : Fin r) : Fn k r ℂ := fun c _ => star (c l)
def aCbi (k : ℕ) {r : ℕ} (l : Fin r) : Fn k r ℂ := fun c _ => (star (c l))⁻¹
def aG (k : ℕ) {r : ℕ} (l : Fin r) : Fn k r ℂ := fun c _ => ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ)
def aY (z : Fin (2 * r + k + 1) → ℂ) (L : Fin (r + 1)) (x : Fin (mdim k r L)) : Fn k r ℂ :=
  fun _ g => yv k r z L g x
def aYb (z : Fin (2 * r + k + 1) → ℂ) (L : Fin (r + 1)) (w : Fin (mdim k r L)) : Fn k r ℂ :=
  fun _ g => ybv k r z L g w

theorem sf_aC (l : Fin r) : SmoothFam k r L (UU Dc) (aC k l) :=
  Qx3.sf_ofC (Qx3.cd_coord l).contDiffOn (fun _ hx => hx.1)
theorem sf_aCb (l : Fin r) : SmoothFam k r L (UU Dc) (aCb k l) :=
  Qx3.sf_ofC (Qx3.cd_coordBar l).contDiffOn (fun _ hx => hx.1)
theorem sf_aCi (l : Fin r) : SmoothFam k r L (UU Dc) (aCi k l) :=
  Qx3.sf_ofC ((Qx3.cd_coord l).contDiffOn.inv fun x (hx : x ∈ OmX r) => hx l) (fun _ hx => hx.1)
theorem sf_aCbi (l : Fin r) : SmoothFam k r L (UU Dc) (aCbi k l) :=
  Qx3.sf_ofC ((Qx3.cd_coordBar l).contDiffOn.inv fun x (hx : x ∈ OmX r) => star_ne_zero.2 (hx l)) (fun _ hx => hx.1)
theorem sf_aG (l : Fin r) : SmoothFam k r L (UU Dc) (aG k l) :=
  Qx3.sf_ofC (cd_gamma l _) (fun _ hx => hx.1)
theorem sf_aY (z : Fin (2 * r + k + 1) → ℂ) (x : Fin (mdim k r L)) : SmoothFam k r L (UU Dc) (aY z L x) :=
  Qx3.sf_yv z x
theorem sf_aYb (z : Fin (2 * r + k + 1) → ℂ) (w : Fin (mdim k r L)) : SmoothFam k r L (UU Dc) (aYb z L w) :=
  Qx3.sf_ybv z w

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mB (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (L : Fin (r + 1)) {Dc : (Fin r → ℂ) → Set (Mx k r)}
    (ho : IsOpen (UU Dc)) {t : ℕ} (a b : Fin t → Fin (mdim k r L)) (u : ℂ) : Module.End ℂ (sfData E L ho).V :=
  (sfData E L ho).hat (grp (qminorOp (EH k r) (posL k r L ∘ a) (posL k r L ∘ b) u))

theorem good_mB (ho : IsOpen (UU Dc)) {t : ℕ} (a b : Fin t → Fin (mdim k r L)) (u : ℂ) :
    (sfData E L ho).Good (grp (qminorOp (EH k r) (posL k r L ∘ a) (posL k r L ∘ b) u)) :=
  sf_good_grp ho (Qx3.pres_qminor a b u) (fun _ hc => (Qx2.good_qminor (open_slice ho hc) a b u).ll)

theorem mulB_apply (ho : IsOpen (UU Dc)) {a : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a) (Ψ : (sfData E L ho).V)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r L) (hgD : g ∈ Dc c) :
    ((mulB E L ho a Ψ : (sfData E L ho).V) : Fn k r E) c g = a c g • (Ψ : Fn k r E) c g :=
  sf_hat_apply ho (sf_good_mul ho ha) Ψ hc hg hgD

end Mult

section Base
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ} {l : Fin r}
  {D : Set (Mx k r)}

theorem int_of (hW : WeylLevelElementFacts) (hD : IsDom k r z z' l.castSucc D)
    {T : Module.End ℂ (levData E l.castSucc hD.1).V} {T' : Module.End ℂ (sfData E l.succ (ho1 l hD.1)).V}
    (h1 : T ∈ keepAlg (VLeft z l.castSucc hD.1))
    (h2 : ∀ F ∈ VLeft z l.castSucc hD.1, ∀ c ∈ OmX r, ∀ x ∈ Glev k r l.succ, x ∈ Dc1 l D c →
      ((T F : (levData E l.castSucc hD.1).V) : Mx k r → E) (w1 k r l (c l) * x) =
        ((T' (rho E hW l hD.1 F) : (sfData E l.succ (ho1 l hD.1)).V) : Fn k r E) c x) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) T T' :=
  ⟨h1, fun F hF => sf_ext _ (fun c hc x hx hxD => by
    rw [rho_apply hW l hD.1 _ hc hx hxD]
    exact h2 F hF c hc x hx hxD)⟩

theorem rho_germ (hW : WeylLevelElementFacts) (hD : IsOpen D) (F : (levData E l.castSucc hD).V) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {x : Mx k r} (hx : x ∈ Glev k r l.succ) (hxD : x ∈ Dc1 l D c) :
    (fun c' => ((rho E hW l hD F : (sfData E l.succ (ho1 l hD)).V) : Fn k r E) c' x) =ᶠ[𝓝 c]
      fun c' => (F : Mx k r → E) (w1 k r l (c' l) * x) := by
  filter_upwards [near_pt (ho1 l hD) hc hxD] with c' hc'
  exact rho_apply hW l hD F hc'.1 hx hc'.2

theorem int_ee (hW : WeylLevelElementFacts) (hEP : EabPres) (hT : RuleTorus) (hD : IsDom k r z z' l.castSucc D) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) (E0 E l.castSucc hD.1 (e0 k l) (e0 k l))
      (opB E l.succ (ho1 l hD.1) l 0) := by
  refine int_of hW hD (level_generator_preserves_left_space hEP hD _ _) (fun F _ c hc x hx hxD => ?_)
  rw [level_generator_apply hD.1 _ _ F (pt_mem hW l hc hx hxD), level_position_first_basis]
  unfold opB
  rw [sf_hat_apply _ (sf_good_crd _ l 0) _ hc hx hxD]
  rw [(hT E k r l D F hD.1 F.2.1 c hc x hx hxD).1]
  exact (opL_germ l 0 (rho_germ hW hD.1 F hc hx hxD)).symm

theorem int_ss (hW : WeylLevelElementFacts) (hEP : EabPres) (hT : RuleTorus) (hD : IsDom k r z z' l.castSucc D) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) (E0 E l.castSucc hD.1 (es0 k l) (es0 k l))
      (-opB E l.succ (ho1 l hD.1) l 3) := by
  refine int_of hW hD (level_generator_preserves_left_space hEP hD _ _) (fun F _ c hc x hx hxD => ?_)
  rw [level_generator_apply hD.1 _ _ F (pt_mem hW l hc hx hxD), level_position_last_basis, LinearMap.neg_apply, Submodule.coe_neg]
  unfold opB
  rw [Pi.neg_apply, Pi.neg_apply, sf_hat_apply _ (sf_good_crd _ l 3) _ hc hx hxD]
  rw [(hT E k r l D F hD.1 F.2.1 c hc x hx hxD).2]
  congr 1
  exact (opL_germ l 3 (rho_germ hW hD.1 F hc hx hxD)).symm

theorem int_minor (hW : WeylLevelElementFacts) (hEP : EabPres) (hQ : QMinorLeftH) (hD : IsDom k r z z' l.castSucc D) {t : ℕ}
    (a b : Fin t → Fin (mdim k r l.succ)) (u : ℂ) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) (qminor (E0 E l.castSucc hD.1) (v0 k l ∘ a) (v0 k l ∘ b) u)
      (mB E l.succ (ho1 l hD.1) a b u) := by
  refine int_of hW hD (keep_qminor _ _ (level_generator_preserves_left_space hEP hD) _ _ _) (fun F _ c hc x hx hxD => ?_)
  rw [quantum_minor_level_apply hD.1 _ _ _ F (pt_mem hW l hc hx hxD), ← Function.comp_assoc, ← Function.comp_assoc,
    level_position_comp_inclusion]
  unfold mB
  rw [sf_hat_apply _ (good_mB _ a b u) _ hc hx hxD]
  have h1 := congrFun (hQ E (2 * r + k + 1) t (Hpk k r) F (posL k r l.succ ∘ a) (posL k r l.succ ∘ b) u
    (w1 k r l (c l))) x
  rw [← h1]
  exact ((Qx2.good_qminor (open_slice (ho1 l hD.1) hc) a b u).loc _ _
    (fun y hy => (rho_apply hW l hD.1 F hc hy.1 hy.2).symm) x ⟨hx, hxD⟩)

theorem int_we (hW : WeylLevelElementFacts) (hEP : EabPres) (hL : RuleLeft) (hz : inWb k r z) (hD : IsDom k r z z' l.castSucc D)
    (w : Fin (mdim k r l.succ)) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) (E0 E l.castSucc hD.1 (v0 k l w) (e0 k l))
      (mulB E l.succ (ho1 l hD.1) (aCi k l) * mulB E l.succ (ho1 l hD.1) (aYb z l.succ w)) := by
  refine int_of hW hD (level_generator_preserves_left_space hEP hD _ _) (fun F hF c hc x hx hxD => ?_)
  rw [level_generator_apply hD.1 _ _ F (pt_mem hW l hc hx hxD), level_position_first_basis, level_position_inclusion, Module.End.mul_apply,
    mulB_apply _ (sf_aCi l) _ hc hx hxD, mulB_apply _ (sf_aYb z w) _ hc hx hxD, rho_apply hW l hD.1 F hc hx hxD,
    smul_smul]
  exact (hL E k r z l D F hz hD.1 F.2.1 (fun g hg n hn => (dom_left hD hg hn).2) hF (c l) (hc l) x hx hxD).1 w

theorem int_sx (hW : WeylLevelElementFacts) (hEP : EabPres) (hL : RuleLeft) (hz : inWb k r z) (hD : IsDom k r z z' l.castSucc D)
    (w : Fin (mdim k r l.succ)) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) (E0 E l.castSucc hD.1 (es0 k l) (v0 k l w))
      (mulB E l.succ (ho1 l hD.1) (aCbi k l) * mulB E l.succ (ho1 l hD.1) (aY z l.succ w)) := by
  refine int_of hW hD (level_generator_preserves_left_space hEP hD _ _) (fun F hF c hc x hx hxD => ?_)
  rw [level_generator_apply hD.1 _ _ F (pt_mem hW l hc hx hxD), level_position_last_basis, level_position_inclusion, Module.End.mul_apply,
    mulB_apply _ (sf_aCbi l) _ hc hx hxD, mulB_apply _ (sf_aY z w) _ hc hx hxD, rho_apply hW l hD.1 F hc hx hxD,
    smul_smul]
  exact (hL E k r z l D F hz hD.1 F.2.1 (fun g hg n hn => (dom_left hD hg hn).2) hF (c l) (hc l) x hx hxD).2.1 w

theorem int_se (hW : WeylLevelElementFacts) (hEP : EabPres) (hL : RuleLeft) (hz : inWb k r z) (hD : IsDom k r z z' l.castSucc D) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) (E0 E l.castSucc hD.1 (es0 k l) (e0 k l)) 0 := by
  refine int_of hW hD (level_generator_preserves_left_space hEP hD _ _) (fun F hF c hc x hx hxD => ?_)
  rw [level_generator_apply hD.1 _ _ F (pt_mem hW l hc hx hxD), level_position_last_basis, level_position_first_basis]
  exact (hL E k r z l D F hz hD.1 F.2.1 (fun g hg n hn => (dom_left hD hg hn).2) hF (c l) (hc l) x hx hxD).2.2

end Base

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section IntJGen
variable {V₀ V₁ : Type*} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  (ρ : V₀ →ₗ[ℂ] V₁) (VL : Submodule ℂ V₀) (J₀ : V₀)

def IntJ (T : Module.End ℂ V₀) (T' : Module.End ℂ V₁) : Prop := T J₀ ∈ VL ∧ ρ (T J₀) = T' (ρ J₀)

variable {ρ VL J₀}

theorem IntQ.toJ {T : Module.End ℂ V₀} {T' : Module.End ℂ V₁} (h : IntQ ρ VL T T') (hJ : J₀ ∈ VL) :
    IntJ ρ VL J₀ T T' := by
  obtain ⟨h1, h2⟩ := h
  exact And.intro (h1 J₀ hJ) (h2 J₀ hJ)

theorem IntQ.mulJ {T S : Module.End ℂ V₀} {T' S' : Module.End ℂ V₁} (h : IntQ ρ VL T T') (h' : IntJ ρ VL J₀ S S') :
    IntJ ρ VL J₀ (T * S) (T' * S') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine And.intro (h1 _ h1') ?_
  show ρ (T (S J₀)) = T' (S' (ρ J₀))
  rw [h2 _ h1', h2']

theorem IntJ.add {T S : Module.End ℂ V₀} {T' S' : Module.End ℂ V₁} (h : IntJ ρ VL J₀ T T')
    (h' : IntJ ρ VL J₀ S S') : IntJ ρ VL J₀ (T + S) (T' + S') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine And.intro (VL.add_mem h1 h1') ?_
  show ρ (T J₀ + S J₀) = T' (ρ J₀) + S' (ρ J₀)
  rw [map_add, h2, h2']

theorem IntJ.neg {T : Module.End ℂ V₀} {T' : Module.End ℂ V₁} (h : IntJ ρ VL J₀ T T') :
    IntJ ρ VL J₀ (-T) (-T') := by
  obtain ⟨h1, h2⟩ := h
  refine And.intro (VL.neg_mem h1) ?_
  show ρ (-T J₀) = -T' (ρ J₀)
  rw [map_neg, h2]

theorem IntJ.sub {T S : Module.End ℂ V₀} {T' S' : Module.End ℂ V₁} (h : IntJ ρ VL J₀ T T')
    (h' : IntJ ρ VL J₀ S S') : IntJ ρ VL J₀ (T - S) (T' - S') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine And.intro (VL.sub_mem h1 h1') ?_
  show ρ (T J₀ - S J₀) = T' (ρ J₀) - S' (ρ J₀)
  rw [map_sub, h2, h2']

theorem intJ_zero : IntJ ρ VL J₀ 0 0 := by
  refine And.intro VL.zero_mem ?_
  show ρ 0 = 0
  exact map_zero ρ

theorem IntJ.intMul {T : Module.End ℂ V₀} {T' : Module.End ℂ V₁} (h : IntJ ρ VL J₀ T T') (n : ℤ) :
    IntJ ρ VL J₀ ((n : Module.End ℂ V₀) * T) ((n : ℂ) • T') := by
  rw [← map_intCast (algebraMap ℂ (Module.End ℂ V₀)) n, Algebra.algebraMap_eq_smul_one, smul_one_mul]
  obtain ⟨h1, h2⟩ := h
  refine And.intro (VL.smul_mem _ h1) ?_
  show ρ ((n : ℂ) • T J₀) = (n : ℂ) • T' (ρ J₀)
  rw [map_smul, h2]

theorem IntJ.sum {ι : Type*} (s : Finset ι) {T : ι → Module.End ℂ V₀} {T' : ι → Module.End ℂ V₁}
    (h : ∀ j ∈ s, IntJ ρ VL J₀ (T j) (T' j)) : IntJ ρ VL J₀ (∑ j ∈ s, T j) (∑ j ∈ s, T' j) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact intJ_zero
  · intro j s hj ih h
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IntJ.ite {T : Module.End ℂ V₀} {T' : Module.End ℂ V₁} (h : IntJ ρ VL J₀ T T') (p : Prop) [Decidable p] :
    IntJ ρ VL J₀ (if p then T else 0) (if p then T' else 0) := by
  split_ifs
  · exact h
  · exact intJ_zero

theorem intJ_eig (hJ : J₀ ∈ VL) {S : Module.End ℂ V₀} {s : ℂ} (h : S J₀ = s • J₀) :
    IntJ ρ VL J₀ S (s • (1 : Module.End ℂ V₁)) := by
  refine And.intro ?_ ?_
  · rw [h]
    exact VL.smul_mem s hJ
  · show ρ (S J₀) = s • ρ J₀
    rw [h, map_smul]

theorem intertwines_product_of_eigenvalues (hJ : J₀ ∈ VL) {S S' : Module.End ℂ V₀} {s s' : ℂ} (h : S J₀ = s • J₀) (h' : S' J₀ = s' • J₀) :
    IntJ ρ VL J₀ (S * S') ((s * s') • (1 : Module.End ℂ V₁)) := by
  have hSS : (S * S') J₀ = (s * s') • J₀ := by
    show S (S' J₀) = _
    rw [h', map_smul, h, smul_smul, mul_comm]
  refine And.intro ?_ ?_
  · rw [hSS]
    exact VL.smul_mem _ hJ
  · show ρ ((S * S') J₀) = (s * s') • ρ J₀
    rw [hSS, map_smul]

theorem intJ_zero_right {T S : Module.End ℂ V₀} (h : S J₀ = 0) : IntJ ρ VL J₀ (T * S) 0 := by
  have h0 : (T * S) J₀ = 0 := by
    show T (S J₀) = 0
    rw [h, map_zero]
  refine And.intro ?_ ?_
  · rw [h0]
    exact VL.zero_mem
  · show ρ ((T * S) J₀) = 0
    rw [h0, map_zero]

theorem intJ_zero_left (hJ : J₀ ∈ VL) {T X : Module.End ℂ V₀} (h : IntQ ρ VL T 0) (hX : X ∈ keepAlg VL) :
    IntJ ρ VL J₀ (T * X) 0 := by
  obtain ⟨h1, h2⟩ := h
  have hXJ : X J₀ ∈ VL := (show ∀ F ∈ VL, X F ∈ VL from hX) J₀ hJ
  refine And.intro (h1 _ hXJ) ?_
  show ρ (T (X J₀)) = 0
  rw [h2 _ hXJ, LinearMap.zero_apply]

end IntJGen

section Border
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} {E : Fin n → Fin n → A} {e es : Fin n} {v : Fin m → Fin n}

theorem borderFull' (hB : BorderFull) (hE : GlRel E) (hv : IsBorder e es v) (u : ℂ) :
    qminor E (bE e (bS v es)) (bE e (bS v es)) u =
        Tm E (u - (m : ℂ) - 1) es es * qminor E v v (u - 1) * Tm E u e e
        - (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E es (v x) * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 1) * Tm E u e e * E (v w) es))
        - (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (Tm E (u - (m : ℂ) - 1) es es * E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * E e (v x)))
        - (∑ w : Fin m, ∑ w' : Fin m, ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0)
        + (((-1 : ℤ) ^ (m + 1) : ℤ) : A) * (E es e * qminor E (bE e v) (bS v es) (u - 1))
        + ∑ w : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + 1 + m) : ℤ) : A) *
            (E (v w) e * qminor E (Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast (by
                have := w.isLt; omega)) v (u - 1) * E e es) := by
  rw [hB A n m E e es v hE hv u]
  obtain ⟨_, hee, hve, hvs⟩ := hv
  have c1 : Tm E u e e * qminor E v v (u - 1) * Tm E (u - (m : ℂ) - 1) es es =
      Tm E (u - (m : ℂ) - 1) es es * qminor E v v (u - 1) * Tm E u e e := by
    have h1 := (commute_Tm_qminor hE u (u - 1) hve hve).eq
    have h2 := (commute_Tm_qminor hE (u - (m : ℂ) - 1) (u - 1) hvs hvs).eq
    have h3 := (commute_Tm_Tm hE u (u - (m : ℂ) - 1) hee hee.symm).eq
    rw [h1, mul_assoc, h3, ← mul_assoc, ← h2]
  have c2 : ∀ w x : Fin m, E es (v x) * Tm E u e e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 1) * E (v w) es =
      E es (v x) * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 1) * Tm E u e e * E (v w) es := by
    intro w x
    have h1 := (commute_Tm_qminor hE u (u - 1) (a := v ∘ skip1 w) (b := v ∘ skip1 x) (fun i => hve _)
      (fun i => hve _)).eq
    rw [mul_assoc (E es (v x)), h1, ← mul_assoc]
  have c3 : ∀ w x : Fin m, E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) *
        Tm E (u - (m : ℂ) - 1) es es * E e (v x) =
      Tm E (u - (m : ℂ) - 1) es es * E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * E e (v x) := by
    intro w x
    have h1 := (commute_Tm_qminor hE (u - (m : ℂ) - 1) (u - 2) (a := v ∘ skip1 w) (b := v ∘ skip1 x)
      (fun i => hvs _) (fun i => hvs _)).eq
    have h2 := (commute_Tm_E hE (u - (m : ℂ) - 1) (hvs w).symm hee).eq
    rw [mul_assoc (E (v w) e), ← h1, ← mul_assoc, ← h2]
  simp only [c1, c2, c3]

end Border

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Eval
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ} {l : Fin r}
  {D : Set (Mx k r)}

def J0 (hD : IsOpen D) {J : Mx k r → E} (hJ : SmoothLev k r l.castSucc D J) : (levData E l.castSucc hD).V :=
  (levData E l.castSucc hD).toV J hJ

theorem restricted_function_on_level (hD : IsOpen D) {J : Mx k r → E} (hJ : SmoothLev k r l.castSucc D J) {g : Mx k r}
    (hg : g ∈ Glev k r l.castSucc ∩ D) : ((J0 hD hJ : (levData E l.castSucc hD).V) : Mx k r → E) g = J g :=
  level_restriction_apply_on J hg

theorem restricted_function_mem_left_space (hD : IsDom k r z z' l.castSucc D) {J : Mx k r → E} (hJ : SmoothLev k r l.castSucc D J)
    (hl : LeftEq k r z l.castSucc D J) : J0 hD.1 hJ ∈ VLeft z l.castSucc hD.1 := by
  intro g hg n hn
  rw [restricted_function_on_level hD.1 hJ hg, restricted_function_on_level hD.1 hJ (dom_left hD hg hn)]
  exact hl g hg n hn

theorem level_generator_on_restricted_function (hD : IsOpen D) {J : Mx k r → E} (hJ : SmoothLev k r l.castSucc D J)
    (a b : Fin (mdim k r l.castSucc)) {g : Mx k r} (hg : g ∈ Glev k r l.castSucc ∩ D) :
    ((E0 E l.castSucc hD a b (J0 hD hJ) : (levData E l.castSucc hD).V) : Mx k r → E) g =
      EH k r (posL k r l.castSucc a) (posL k r l.castSucc b) J g := by
  unfold E0 J0
  rw [HatData.hat_toV (level_generator_good hD a b) hJ]
  exact level_restriction_apply_on _ hg

theorem eig_ex (hRR : RuleRight) (hz' : inWb k r z') (hD : IsOpen D) {J : Mx k r → E}
    (hJ : SmoothLev k r l.castSucc D J) (hr : RightEq k r z' l.castSucc D J) (x : Fin (mdim k r l.succ)) :
    E0 E l.castSucc hD (e0 k l) (v0 k l x) (J0 hD hJ) = xv k r z' l.succ x • J0 hD hJ := by
  refine lev_ext hD (fun g hg => ?_)
  rw [level_generator_on_restricted_function hD hJ _ _ hg, level_position_first_basis, level_position_inclusion, Submodule.coe_smul, Pi.smul_apply, restricted_function_on_level hD hJ hg]
  exact (hRR E k r z' l D J hz' hD hJ hr g hg).1 x

theorem eig_ws (hRR : RuleRight) (hz' : inWb k r z') (hD : IsOpen D) {J : Mx k r → E}
    (hJ : SmoothLev k r l.castSucc D J) (hr : RightEq k r z' l.castSucc D J) (w : Fin (mdim k r l.succ)) :
    E0 E l.castSucc hD (v0 k l w) (es0 k l) (J0 hD hJ) = xbv k r z' l.succ w • J0 hD hJ := by
  refine lev_ext hD (fun g hg => ?_)
  rw [level_generator_on_restricted_function hD hJ _ _ hg, level_position_last_basis, level_position_inclusion, Submodule.coe_smul, Pi.smul_apply, restricted_function_on_level hD hJ hg]
  exact (hRR E k r z' l D J hz' hD hJ hr g hg).2.1 w

theorem eig_es (hRR : RuleRight) (hz' : inWb k r z') (hD : IsOpen D) {J : Mx k r → E}
    (hJ : SmoothLev k r l.castSucc D J) (hr : RightEq k r z' l.castSucc D J) :
    E0 E l.castSucc hD (e0 k l) (es0 k l) (J0 hD hJ) = 0 := by
  refine lev_ext hD (fun g hg => ?_)
  rw [level_generator_on_restricted_function hD hJ _ _ hg, level_position_first_basis, level_position_last_basis]
  exact (hRR E k r z' l D J hz' hD hJ hr g hg).2.2

variable (E l) in
def bTee (hD : IsOpen D) (u : ℂ) : Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  u • 1 + opB E l.succ (ho1 l hD) l 0

variable (E l) in
def bTss (hD : IsOpen D) (u : ℂ) : Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  u • 1 - opB E l.succ (ho1 l hD) l 3

variable (E l) in
def scaledRowVectorOperator (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (w : Fin (mdim k r l.succ)) :
    Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  mulB E l.succ (ho1 l hD) (aCi k l) * mulB E l.succ (ho1 l hD) (aYb z l.succ w)

variable (E l) in
def scaledColumnVectorOperator (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (x : Fin (mdim k r l.succ)) :
    Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  mulB E l.succ (ho1 l hD) (aCbi k l) * mulB E l.succ (ho1 l hD) (aY z l.succ x)

theorem int_Tee (hW : WeylLevelElementFacts) (hEP : EabPres) (hT : RuleTorus) (hD : IsDom k r z z' l.castSucc D) (u : ℂ) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) (Tm (E0 E l.castSucc hD.1) u (e0 k l) (e0 k l))
      (bTee E l hD.1 u) := by
  have := (int_algebraMap (ρ := rho E hW l hD.1) (VL := VLeft z l.castSucc hD.1) u).add (int_ee hW hEP hT hD)
  rw [Algebra.algebraMap_eq_smul_one (A := Module.End ℂ (sfData E l.succ (ho1 l hD.1)).V)] at this
  simpa only [Tm, if_true, bTee] using this

theorem int_Tss (hW : WeylLevelElementFacts) (hEP : EabPres) (hT : RuleTorus) (hD : IsDom k r z z' l.castSucc D) (u : ℂ) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) (Tm (E0 E l.castSucc hD.1) u (es0 k l) (es0 k l))
      (bTss E l hD.1 u) := by
  have := (int_algebraMap (ρ := rho E hW l hD.1) (VL := VLeft z l.castSucc hD.1) u).add (int_ss hW hEP hT hD)
  rw [Algebra.algebraMap_eq_smul_one (A := Module.End ℂ (sfData E l.succ (ho1 l hD.1)).V), ← sub_eq_add_neg] at this
  simpa only [Tm, if_true, bTss] using this

theorem int_C (hW : WeylLevelElementFacts) (hEP : EabPres) (hQ : QMinorLeftH) (hD : IsDom k r z z' l.castSucc D) (u : ℂ) :
    IntQ (rho E hW l hD.1) (VLeft z l.castSucc hD.1) (qminor (E0 E l.castSucc hD.1) (v0 k l) (v0 k l) u)
      (mB E l.succ (ho1 l hD.1) id id u) := int_minor hW hEP hQ hD id id u

variable (E l) in

def bE1 (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (u : ℂ) : Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  mB E l.succ (ho1 l hD) id id (u - 1) * bTee E l hD u -
    ∑ w : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ), ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (scaledRowVectorOperator E l hD z w * mB E l.succ (ho1 l hD) (skip1 w) (skip1 x) (u - 2) * (xv k r z' l.succ x • 1))

variable (E l) in

def borderedMinorLastColumn (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (u : ℂ) : Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  bTss E l hD (u - (mdim k r l.succ : ℂ)) * mB E l.succ (ho1 l hD) id id u -
    ∑ w : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ), ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (scaledColumnVectorOperator E l hD z x * mB E l.succ (ho1 l hD) (skip1 w) (skip1 x) u * (xbv k r z' l.succ w • 1))

variable (E l) in

def doubleRemovedMinorTerm (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (u : ℂ) : Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  ∑ w : Fin (mdim k r l.succ), ∑ w' : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ),
    ∑ x' : Fin (mdim k r l.succ), if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : ℂ) •
      (scaledRowVectorOperator E l hD z w * scaledColumnVectorOperator E l hD z x *
        mB E l.succ (ho1 l hD) (skip2 (min w w') (max w w')) (skip2 (min x x') (max x x')) (u - 2) *
        ((xv k r z' l.succ x' * xbv k r z' l.succ w') • 1)) else 0

variable (E l) in

def capelliDetFirstFactorOrder (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (u : ℂ) : Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  bTee E l hD u * mB E l.succ (ho1 l hD) id id (u - 1) * bTss E l hD (u - (mdim k r l.succ : ℂ) - 1)
  - (∑ w : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ), ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (scaledColumnVectorOperator E l hD z x * bTee E l hD u * mB E l.succ (ho1 l hD) (skip1 w) (skip1 x) (u - 1) *
        (xbv k r z' l.succ w • 1)))
  - (∑ w : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ), ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (scaledRowVectorOperator E l hD z w * mB E l.succ (ho1 l hD) (skip1 w) (skip1 x) (u - 2) *
        bTss E l hD (u - (mdim k r l.succ : ℂ) - 1) * (xv k r z' l.succ x • 1)))
  - doubleRemovedMinorTerm E l hD z z' u

variable (E l) in

def capelliDetSecondFactorOrder (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (u : ℂ) : Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  bTss E l hD (u - (mdim k r l.succ : ℂ) - 1) * mB E l.succ (ho1 l hD) id id (u - 1) * bTee E l hD u
  - (∑ w : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ), ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (scaledColumnVectorOperator E l hD z x * mB E l.succ (ho1 l hD) (skip1 w) (skip1 x) (u - 1) * bTee E l hD u *
        (xbv k r z' l.succ w • 1)))
  - (∑ w : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ), ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (bTss E l hD (u - (mdim k r l.succ : ℂ) - 1) * scaledRowVectorOperator E l hD z w *
        mB E l.succ (ho1 l hD) (skip1 w) (skip1 x) (u - 2) * (xv k r z' l.succ x • 1)))
  - doubleRemovedMinorTerm E l hD z z' u

structure Rules : Prop where
  gl : EabGlLev
  ep : EabPres
  q : QMinorLeftH
  rr : RuleRight
  rl : RuleLeft
  rt : RuleTorus
  w : WeylLevelElementFacts

variable (R : Rules) (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' l.castSucc D) {J : Mx k r → E}
  (hJ : SmoothLev k r l.castSucc D J) (hl : LeftEq k r z l.castSucc D J) (hr : RightEq k r z' l.castSucc D J)

include hz hz' hl hr in
theorem evalE (hB : BorderE) (u : ℂ) :
    IntJ (rho E R.w l hD.1) (VLeft z l.castSucc hD.1) (J0 hD.1 hJ)
      (qminor (E0 E l.castSucc hD.1) (bE (e0 k l) (v0 k l)) (bE (e0 k l) (v0 k l)) u) (bE1 E l hD.1 z z' u) := by
  rw [borderE' hB (level_generators_gl_relations R.gl l.castSucc hD.1) (isBorder0 k l) u]
  have hJ0 := restricted_function_mem_left_space hD hJ hl
  refine IntJ.sub (((int_C R.w R.ep R.q hD (u - 1)).mul (int_Tee R.w R.ep R.rt hD u)).toJ hJ0)
    (IntJ.sum _ fun w _ => IntJ.sum _ fun x _ => IntJ.intMul ?_ _)
  exact ((int_we R.w R.ep R.rl hz hD w).mul (int_minor R.w R.ep R.q hD (skip1 w) (skip1 x) (u - 2))).mulJ
    (intJ_eig hJ0 (eig_ex R.rr hz' hD.1 hJ hr x))

include hz hz' hl hr in
theorem evalS (hB : BorderS) (u : ℂ) :
    IntJ (rho E R.w l hD.1) (VLeft z l.castSucc hD.1) (J0 hD.1 hJ)
      (qminor (E0 E l.castSucc hD.1) (bS (v0 k l) (es0 k l)) (bS (v0 k l) (es0 k l)) u) (borderedMinorLastColumn E l hD.1 z z' u) := by
  rw [borderS' (e := e0 k l) hB (level_generators_gl_relations R.gl l.castSucc hD.1) (isBorder0 k l) u]
  have hJ0 := restricted_function_mem_left_space hD hJ hl
  refine IntJ.sub (((int_Tss R.w R.ep R.rt hD _).mul (int_C R.w R.ep R.q hD u)).toJ hJ0)
    (IntJ.sum _ fun w _ => IntJ.sum _ fun x _ => IntJ.intMul ?_ _)
  exact ((int_sx R.w R.ep R.rl hz hD x).mul (int_minor R.w R.ep R.q hD (skip1 w) (skip1 x) u)).mulJ
    (intJ_eig hJ0 (eig_ws R.rr hz' hD.1 hJ hr w))

include hz hz' hl hr in
theorem eval_two_removed_term_on_level (u : ℂ) :
    IntJ (rho E R.w l hD.1) (VLeft z l.castSucc hD.1) (J0 hD.1 hJ)
      (∑ w : Fin (mdim k r l.succ), ∑ w' : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ),
        ∑ x' : Fin (mdim k r l.succ),
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : Module.End ℂ (levData E l.castSucc hD.1).V) *
              (E0 E l.castSucc hD.1 (v0 k l w) (e0 k l) * E0 E l.castSucc hD.1 (es0 k l) (v0 k l x) *
                qminor (E0 E l.castSucc hD.1) (v0 k l ∘ skip2 (min w w') (max w w'))
                  (v0 k l ∘ skip2 (min x x') (max x x')) (u - 2) *
                E0 E l.castSucc hD.1 (e0 k l) (v0 k l x') * E0 E l.castSucc hD.1 (v0 k l w') (es0 k l))
            else 0) (doubleRemovedMinorTerm E l hD.1 z z' u) := by
  have hJ0 := restricted_function_mem_left_space hD hJ hl
  refine IntJ.sum _ fun w _ => IntJ.sum _ fun w' _ => IntJ.sum _ fun x _ => IntJ.sum _ fun x' _ =>
    IntJ.ite (IntJ.intMul ?_ _) _
  rw [mul_assoc _ (E0 E l.castSucc hD.1 (e0 k l) (v0 k l x')) _]
  exact (((int_we R.w R.ep R.rl hz hD w).mul (int_sx R.w R.ep R.rl hz hD x)).mul
    (int_minor R.w R.ep R.q hD _ _ (u - 2))).mulJ
    (intertwines_product_of_eigenvalues hJ0 (eig_ex R.rr hz' hD.1 hJ hr x') (eig_ws R.rr hz' hD.1 hJ hr w'))

include hz hz' hl hr in
theorem capelli_det_first_order_intertwines (hB : BorderFull) (u : ℂ) :
    IntJ (rho E R.w l hD.1) (VLeft z l.castSucc hD.1) (J0 hD.1 hJ)
      (qminor (E0 E l.castSucc hD.1) (bE (e0 k l) (bS (v0 k l) (es0 k l))) (bE (e0 k l) (bS (v0 k l) (es0 k l))) u)
      (capelliDetFirstFactorOrder E l hD.1 z z' u) := by
  rw [hB _ _ _ _ _ _ _ (level_generators_gl_relations R.gl l.castSucc hD.1) (isBorder0 k l) u]
  have hJ0 := restricted_function_mem_left_space hD hJ hl
  have t1 := (((int_Tee R.w R.ep R.rt hD u).mul (int_C R.w R.ep R.q hD (u - 1))).mul
    (int_Tss R.w R.ep R.rt hD (u - (mdim k r l.succ : ℂ) - 1))).toJ hJ0
  have t2 := IntJ.sum Finset.univ fun (w : Fin (mdim k r l.succ)) _ => IntJ.sum Finset.univ
    fun (x : Fin (mdim k r l.succ)) _ => IntJ.intMul ((((int_sx R.w R.ep R.rl hz hD x).mul
      (int_Tee R.w R.ep R.rt hD u)).mul (int_minor R.w R.ep R.q hD (skip1 w) (skip1 x) (u - 1))).mulJ
      (intJ_eig hJ0 (eig_ws R.rr hz' hD.1 hJ hr w))) ((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)))
  have t3 := IntJ.sum Finset.univ fun (w : Fin (mdim k r l.succ)) _ => IntJ.sum Finset.univ
    fun (x : Fin (mdim k r l.succ)) _ => IntJ.intMul ((((int_we R.w R.ep R.rl hz hD w).mul
      (int_minor R.w R.ep R.q hD (skip1 w) (skip1 x) (u - 2))).mul
      (int_Tss R.w R.ep R.rt hD (u - (mdim k r l.succ : ℂ) - 1))).mulJ
      (intJ_eig hJ0 (eig_ex R.rr hz' hD.1 hJ hr x))) ((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)))
  have t4 := eval_two_removed_term_on_level R hz hz' hD hJ hl hr u
  have t5 := IntJ.intMul (intJ_zero_left hJ0 (int_se R.w R.ep R.rl hz hD)
    (keep_qminor _ _ (level_generator_preserves_left_space R.ep hD) (bE (e0 k l) (v0 k l)) (bS (v0 k l) (es0 k l)) (u - 1)))
    ((-1 : ℤ) ^ (mdim k r l.succ + 1))
  have t6 := IntJ.sum (ρ := rho E R.w l hD.1) (VL := VLeft z l.castSucc hD.1) (J₀ := J0 hD.1 hJ) Finset.univ
    fun (w : Fin (mdim k r l.succ)) _ => IntJ.intMul (intJ_zero_right
      (T := E0 E l.castSucc hD.1 (v0 k l w) (e0 k l) * qminor (E0 E l.castSucc hD.1)
        (Fin.snoc (α := fun _ => Fin (mdim k r l.castSucc)) (v0 k l ∘ skip1 w) (es0 k l) ∘ Fin.cast (by
                have := w.isLt; omega)) (v0 k l) (u - 1)) (eig_es R.rr hz' hD.1 hJ hr))
      ((-1 : ℤ) ^ ((w : ℕ) + 1 + mdim k r l.succ))
  have h := ((((t1.sub t2).sub t3).sub t4).add t5).add t6
  simpa only [smul_zero, Finset.sum_const_zero, add_zero, capelliDetFirstFactorOrder, scaledRowVectorOperator, scaledColumnVectorOperator] using h

include hz hz' hl hr in
theorem capelli_det_second_order_intertwines (hB : BorderFull) (u : ℂ) :
    IntJ (rho E R.w l hD.1) (VLeft z l.castSucc hD.1) (J0 hD.1 hJ)
      (qminor (E0 E l.castSucc hD.1) (bE (e0 k l) (bS (v0 k l) (es0 k l))) (bE (e0 k l) (bS (v0 k l) (es0 k l))) u)
      (capelliDetSecondFactorOrder E l hD.1 z z' u) := by
  rw [borderFull' hB (level_generators_gl_relations R.gl l.castSucc hD.1) (isBorder0 k l) u]
  have hJ0 := restricted_function_mem_left_space hD hJ hl
  have t1 := (((int_Tss R.w R.ep R.rt hD (u - (mdim k r l.succ : ℂ) - 1)).mul (int_C R.w R.ep R.q hD (u - 1))).mul
    (int_Tee R.w R.ep R.rt hD u)).toJ hJ0
  have t2 := IntJ.sum Finset.univ fun (w : Fin (mdim k r l.succ)) _ => IntJ.sum Finset.univ
    fun (x : Fin (mdim k r l.succ)) _ => IntJ.intMul ((((int_sx R.w R.ep R.rl hz hD x).mul
      (int_minor R.w R.ep R.q hD (skip1 w) (skip1 x) (u - 1))).mul (int_Tee R.w R.ep R.rt hD u)).mulJ
      (intJ_eig hJ0 (eig_ws R.rr hz' hD.1 hJ hr w))) ((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)))
  have t3 := IntJ.sum Finset.univ fun (w : Fin (mdim k r l.succ)) _ => IntJ.sum Finset.univ
    fun (x : Fin (mdim k r l.succ)) _ => IntJ.intMul ((((int_Tss R.w R.ep R.rt hD (u - (mdim k r l.succ : ℂ) - 1)).mul
      (int_we R.w R.ep R.rl hz hD w)).mul (int_minor R.w R.ep R.q hD (skip1 w) (skip1 x) (u - 2))).mulJ
      (intJ_eig hJ0 (eig_ex R.rr hz' hD.1 hJ hr x))) ((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)))
  have t4 := eval_two_removed_term_on_level R hz hz' hD hJ hl hr u
  have t5 := IntJ.intMul (intJ_zero_left hJ0 (int_se R.w R.ep R.rl hz hD)
    (keep_qminor _ _ (level_generator_preserves_left_space R.ep hD) (bE (e0 k l) (v0 k l)) (bS (v0 k l) (es0 k l)) (u - 1)))
    ((-1 : ℤ) ^ (mdim k r l.succ + 1))
  have t6 := IntJ.sum (ρ := rho E R.w l hD.1) (VL := VLeft z l.castSucc hD.1) (J₀ := J0 hD.1 hJ) Finset.univ
    fun (w : Fin (mdim k r l.succ)) _ => IntJ.intMul (intJ_zero_right
      (T := E0 E l.castSucc hD.1 (v0 k l w) (e0 k l) * qminor (E0 E l.castSucc hD.1)
        (Fin.snoc (α := fun _ => Fin (mdim k r l.castSucc)) (v0 k l ∘ skip1 w) (es0 k l) ∘ Fin.cast (by
                have := w.isLt; omega)) (v0 k l) (u - 1)) (eig_es R.rr hz' hD.1 hJ hr))
      ((-1 : ℤ) ^ ((w : ℕ) + 1 + mdim k r l.succ))
  have h := ((((t1.sub t2).sub t3).sub t4).add t5).add t6
  simpa only [smul_zero, Finset.sum_const_zero, add_zero, capelliDetSecondFactorOrder, scaledRowVectorOperator, scaledColumnVectorOperator] using h

end Eval

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section CellPt

theorem cell_hpk_e (l : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (eI k r l) = v (esI k r l) := by
  simp [Matrix.mulVec, dotProduct, Qx3.hpk_row_e]

theorem cell_hpk_es (l : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (esI k r l) = v (eI k r l) := by
  simp [Matrix.mulVec, dotProduct, Qx3.hpk_row_es]

theorem cell_herm_bvec (v : Fin (2 * r + k + 1) → ℂ) (q : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec q) = (Hpk k r *ᵥ v) q := by
  simp [herm, bvec, dotProduct, Pi.single_apply]

theorem cell_mulVec_bvec (g : Mx k r) (p q : Fin (2 * r + k + 1)) : (g *ᵥ bvec q) p = g p q := by
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

theorem cell_fvec (z : Fin (2 * r + k + 1) → ℂ) (l : Fin r) : fvec k r z l.castSucc = bvec (eI k r l) := by
  unfold fvec
  rw [dif_pos (by simp)]
  rfl

theorem cell_posL_inj {i : Fin (r + 1)} {j j' : Fin (mdim k r i)} (h : posL k r i j = posL k r i j') : j = j' := by
  have h' := congrArg Fin.val h
  simp only [posL] at h'
  exact Fin.ext (by omega)

theorem cell_posL_e (l : Fin r) (j : Fin (mdim k r l.castSucc)) :
    posL k r l.castSucc j = eI k r l ↔ j = e0 k l := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    simp only [posL, eI, Fin.coe_castSucc] at h'
    apply Fin.ext
    show j.val = 0
    omega
  · intro h
    subst h
    exact level_position_first_basis k l

theorem cell_posL_es (l : Fin r) (j : Fin (mdim k r l.castSucc)) :
    posL k r l.castSucc j = esI k r l ↔ j = es0 k l := by
  have hl := l.isLt
  constructor
  · intro h
    have h' := congrArg Fin.val h
    simp only [posL, esI, Fin.coe_castSucc] at h'
    apply Fin.ext
    simp only [es0, mdim, Fin.val_succ]
    omega
  · intro h
    subst h
    exact level_position_last_basis k l

theorem first_basis_index_val_zero (l : Fin r) : (e0 k l : ℕ) = 0 := rfl

theorem first_basis_lt_last_basis (l : Fin r) : e0 k l < es0 k l := by
  rw [Fin.lt_iff_val_lt_val, first_basis_index_val_zero]
  show 0 < mdim k r l.succ + 1
  omega

theorem ne_first_basis_of_lt {l : Fin r} {i i' : Fin (mdim k r l.castSucc)} (h : i < i') : i' ≠ e0 k l := by
  intro h'
  rw [Fin.lt_iff_val_lt_val, h', first_basis_index_val_zero] at h
  omega

theorem cell_es_fix (l : Fin r) {g₁ : Mx k r} (hg₁ : g₁ ∈ Glev k r l.succ) :
    g₁ *ᵥ bvec (esI k r l) = bvec (esI k r l) :=
  (hg₁.2 l (by simp)).2

theorem lower_level_matrix_unit_entry (l : Fin r) {g₁ : Mx k r} (hg₁ : g₁ ∈ Glev k r l.succ) (p : Fin (2 * r + k + 1)) :
    g₁ (eI k r l) p = if p = eI k r l then 1 else 0 := by
  rw [← cell_mulVec_bvec g₁ (eI k r l) p, ← cell_hpk_es l (g₁ *ᵥ bvec p), ← cell_herm_bvec (g₁ *ᵥ bvec p) (esI k r l), ← cell_es_fix l hg₁, Qx2.herm_uh hg₁.1,
    cell_herm_bvec, cell_hpk_es l]
  simp [bvec, Pi.single_apply, eq_comm]

theorem cell_ybv (z : Fin (2 * r + k + 1) → ℂ) (l : Fin r) (c : ℂ) {g₁ : Mx k r} (hg₁ : g₁ ∈ Glev k r l.succ)
    (j : Fin (mdim k r l.castSucc)) :
    ybv k r z l.castSucc (w1 k r l c * g₁) j = if j = e0 k l then c else 0 := by
  unfold ybv
  rw [cell_fvec, cell_herm_bvec, cell_hpk_e, cell_mulVec_bvec, Qx3.weyl_cell_mul_apply, Qx3.sw_es, Qx3.dd_e,
    lower_level_matrix_unit_entry l hg₁]
  by_cases h : j = e0 k l
  · subst h
    simp [level_position_first_basis]
  · have : posL k r l.castSucc j ≠ eI k r l := fun h' => h ((cell_posL_e l j).1 h')
    simp [h, this]

theorem reflection_maps_last_to_first_vector (l : Fin r) (c : ℂ) :
    w1 k r l c *ᵥ bvec (esI k r l) = (star c)⁻¹ • bvec (eI k r l) := by
  funext p
  rw [cell_mulVec_bvec, Qx3.w1_apply, Qx3.sw_es, Qx3.dd_es]
  by_cases h : p = eI k r l
  · subst h
    simp [bvec]
  · simp [h, bvec]

theorem cell_inv (l : Fin r) {c : ℂ} (hc : c ≠ 0) {g₁ : Mx k r} (hg₁ : g₁ ∈ Glev k r l.succ) :
    (w1 k r l c * g₁)⁻¹ *ᵥ bvec (eI k r l) = star c • bvec (esI k r l) := by
  have hu : IsUnit (w1 k r l c * g₁).det := by
    rw [Matrix.det_mul]
    exact (WeylGroupFacts.isUnit_of_uh (Qx3.weyl_cell_mem_unitary l hc)).mul (WeylGroupFacts.isUnit_of_uh hg₁.1)
  have hcs : star c ≠ 0 := star_ne_zero.2 hc
  have hv : (w1 k r l c * g₁) *ᵥ (star c • bvec (esI k r l)) = bvec (eI k r l) := by
    rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, cell_es_fix l hg₁, reflection_maps_last_to_first_vector, smul_smul,
      mul_inv_cancel₀ hcs, one_smul]
  rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem cell_yv (z : Fin (2 * r + k + 1) → ℂ) (l : Fin r) {c : ℂ} (hc : c ≠ 0) {g₁ : Mx k r}
    (hg₁ : g₁ ∈ Glev k r l.succ) (j : Fin (mdim k r l.castSucc)) :
    yv k r z l.castSucc (w1 k r l c * g₁) j = if j = es0 k l then star c else 0 := by
  unfold yv
  rw [cell_fvec, cell_inv l hc hg₁]
  by_cases h : j = es0 k l
  · subst h
    simp [level_position_last_basis, bvec]
  · have : posL k r l.castSucc j ≠ esI k r l := fun h' => h ((cell_posL_es l j).1 h')
    simp [h, this, bvec]

theorem cell_xv (z' : Fin (2 * r + k + 1) → ℂ) (l : Fin r) (j : Fin (mdim k r l.castSucc)) :
    xv k r z' l.castSucc j = if j = e0 k l then 1 else 0 := by
  unfold xv
  rw [cell_fvec]
  by_cases h : j = e0 k l
  · subst h
    simp [level_position_first_basis, bvec]
  · have : posL k r l.castSucc j ≠ eI k r l := fun h' => h ((cell_posL_e l j).1 h')
    simp [h, this, bvec]

theorem cell_xbv (z' : Fin (2 * r + k + 1) → ℂ) (l : Fin r) (j : Fin (mdim k r l.castSucc)) :
    xbv k r z' l.castSucc j = if j = es0 k l then 1 else 0 := by
  unfold xbv
  rw [cell_fvec, cell_herm_bvec, cell_hpk_e]
  by_cases h : j = es0 k l
  · subst h
    simp [level_position_last_basis, bvec]
  · have : posL k r l.castSucc j ≠ esI k r l := fun h' => h ((cell_posL_es l j).1 h')
    simp [h, this, bvec]

theorem double_sum_delta_collapse {X : Type*} [AddCommGroup X] [Module ℂ X] {n : ℕ} (s : Fin n → Fin n → ℂ) (a b : Fin n)
    (α β : ℂ) (M : Fin n → Fin n → X) :
    (∑ i, ∑ j, (s i j * (if i = a then α else 0) * (if j = b then β else 0)) • M i j) =
      (s a b * α * β) • M a b := by
  rw [Fintype.sum_eq_single a, Fintype.sum_eq_single b]
  · simp
  all_goals
    intro x hx
    simp [hx]

theorem quadruple_sum_delta_collapse {X : Type*} [AddCommMonoid X] {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → X) (a b c d : Fin n) :
    (∑ i, ∑ i', ∑ j, ∑ j', if i = a ∧ i' = b ∧ j = c ∧ j' = d then F i i' j j' else 0) = F a b c d := by
  rw [Fintype.sum_eq_single a, Fintype.sum_eq_single b, Fintype.sum_eq_single c, Fintype.sum_eq_single d]
  · simp
  all_goals
    intro x hx
    simp [hx]

theorem cell_neg_one_even (n m : ℕ) : ((-1 : ℂ)) ^ (n + m + n + m) = 1 := by
  rw [show n + m + n + m = 2 * (n + m) by ring, pow_mul]
  simp

theorem cell_neg_one_two (n : ℕ) : ((-1 : ℂ)) ^ (n + n) = 1 := by
  rw [← two_mul, pow_mul]
  simp

end CellPt

theorem tL_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ)
    (l : Fin r) (Y : ℂ) (f : Mx k r → E) {c : ℂ} (hc : c ≠ 0) {g₁ : Mx k r} (hg₁ : g₁ ∈ Glev k r l.succ) :
    tL k r z z' l.castSucc Y 0 1 f (w1 k r l c * g₁) =
        -(c • qminorOp (EH k r) (posL k r l.castSucc ∘ skip1 (e0 k l)) (posL k r l.castSucc ∘ skip1 (e0 k l))
          (uC k r l.castSucc Y - 1) f (w1 k r l c * g₁)) ∧
      tL k r z z' l.castSucc Y 1 0 f (w1 k r l c * g₁) =
        -(star c • qminorOp (EH k r) (posL k r l.castSucc ∘ skip1 (es0 k l)) (posL k r l.castSucc ∘ skip1 (es0 k l))
          (uC k r l.castSucc Y) f (w1 k r l c * g₁)) ∧
      tL k r z z' l.castSucc Y 1 1 f (w1 k r l c * g₁) =
        (c * star c) • qminorOp (EH k r) (posL k r l.castSucc ∘ skip2 (e0 k l) (es0 k l))
          (posL k r l.castSucc ∘ skip2 (e0 k l) (es0 k l)) (uC k r l.castSucc Y - 1) f (w1 k r l c * g₁) := by
  refine ⟨?_, ?_, ?_⟩
  · show -(chatL (EH k r) (posL k r l.castSucc) (uC k r l.castSucc Y - 1) (fun _ => xv k r z' l.castSucc)
        (ybv k r z l.castSucc) f (w1 k r l c * g₁)) = _
    congr 1
    unfold chatL
    simp only [cell_ybv z l c hg₁, cell_xv z' l]
    rw [double_sum_delta_collapse (fun i j : Fin (mdim k r l.castSucc) => (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) (e0 k l) (e0 k l) c 1
      (fun i j => qminorOp (EH k r) (posL k r l.castSucc ∘ skip1 i) (posL k r l.castSucc ∘ skip1 j)
        (uC k r l.castSucc Y - 1) f (w1 k r l c * g₁))]
    simp [first_basis_index_val_zero]
  · show -(chatL (EH k r) (posL k r l.castSucc) (uC k r l.castSucc Y) (yv k r z l.castSucc)
        (fun _ => xbv k r z' l.castSucc) f (w1 k r l c * g₁)) = _
    congr 1
    unfold chatL
    simp only [cell_yv z l hc hg₁, cell_xbv z' l]
    rw [double_sum_delta_collapse (fun i j : Fin (mdim k r l.castSucc) => (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) (es0 k l) (es0 k l) 1
      (star c) (fun i j => qminorOp (EH k r) (posL k r l.castSucc ∘ skip1 i) (posL k r l.castSucc ∘ skip1 j)
        (uC k r l.castSucc Y) f (w1 k r l c * g₁))]
    rw [cell_neg_one_two]
    simp
  · show -(chat2L (EH k r) (posL k r l.castSucc) (uC k r l.castSucc Y - 1) (yv k r z l.castSucc)
        (fun _ => xv k r z' l.castSucc) (ybv k r z l.castSucc) (fun _ => xbv k r z' l.castSucc) f
        (w1 k r l c * g₁)) = _
    have hne := (first_basis_lt_last_basis (k := k) l).ne
    rw [show chat2L (EH k r) (posL k r l.castSucc) (uC k r l.castSucc Y - 1) (yv k r z l.castSucc)
        (fun _ => xv k r z' l.castSucc) (ybv k r z l.castSucc) (fun _ => xbv k r z' l.castSucc) f
        (w1 k r l c * g₁) = ∑ i, ∑ i', ∑ j, ∑ j', if i = e0 k l ∧ i' = es0 k l ∧ j = e0 k l ∧ j' = es0 k l then
          (-(c * star c)) • qminorOp (EH k r) (posL k r l.castSucc ∘ skip2 i i') (posL k r l.castSucc ∘ skip2 j j')
            (uC k r l.castSucc Y - 1) f (w1 k r l c * g₁) else 0 from ?_]
    · rw [quadruple_sum_delta_collapse (fun i i' j j' => (-(c * star c)) • qminorOp (EH k r) (posL k r l.castSucc ∘ skip2 i i')
        (posL k r l.castSucc ∘ skip2 j j') (uC k r l.castSucc Y - 1) f (w1 k r l c * g₁))]
      rw [neg_smul, neg_neg]
    · unfold chat2L
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      simp only [cell_yv z l hc hg₁, cell_ybv z l c hg₁, cell_xv z' l, cell_xbv z' l]
      by_cases h : i < i' ∧ j < j'
      · rw [if_pos h]
        have hi' : i' ≠ e0 k l := ne_first_basis_of_lt h.1
        have hj' : j' ≠ e0 k l := ne_first_basis_of_lt h.2
        by_cases hall : i = e0 k l ∧ i' = es0 k l ∧ j = e0 k l ∧ j' = es0 k l
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := hall
          simp only [and_self, ↓reduceIte, hne, hne.symm, cell_neg_one_even]
          congr 1
          ring
        · rw [if_neg hall]
          by_cases a1 : i = e0 k l <;> by_cases a2 : i' = es0 k l <;> by_cases a3 : j = e0 k l <;>
            by_cases a4 : j' = es0 k l <;>
            first
            | (simp [a1, a2, a3, a4, hi', hj', hne, hne.symm]; done)
            | exact absurd ⟨a1, a2, a3, a4⟩ hall
      · rw [if_neg h, if_neg]
        rintro ⟨rfl, rfl, rfl, rfl⟩
        exact h ⟨first_basis_lt_last_basis l, first_basis_lt_last_basis l⟩

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Finset

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.FourierDecayAlt.Q

theorem sg_pairs {X : Type*} [AddCommMonoid X] {m : ℕ} (F : Fin m → Fin m → X) :
    (∑ w, ∑ w', if w ≠ w' then F w w' else 0) = ∑ i, ∑ i', if i < i' then F i i' + F i' i else 0 := by
  have h1 : ∀ w w' : Fin m, (if w ≠ w' then F w w' else 0) =
      (if w < w' then F w w' else 0) + (if w' < w then F w w' else 0) := by
    intro w w'
    rcases lt_trichotomy w w' with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  have h2 : (∑ w, ∑ w', if w' < w then F w w' else 0) = ∑ i, ∑ i', if i < i' then F i' i else 0 :=
    Finset.sum_comm
  simp_rw [h1, Finset.sum_add_distrib]
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  split_ifs <;> simp

theorem sign_pair_of_lt {m : ℕ} {i i' : Fin m} (h : i < i') :
    sg2 i i' = (-1) ^ (i.val + i'.val + 1) ∧ sg2 i' i = (-1) ^ (i.val + i'.val) := by
  have h' : i.val < i'.val := h
  have h1 : ¬ i'.val < i.val := by omega
  refine ⟨by simp only [sg2, if_neg h1], by simp only [sg2, if_pos h', Nat.add_comm]⟩

theorem double_sign_sum_reindex_ordered {R M : Type*} [CommRing R] [AddCommGroup M] {m : ℕ} (β β' a a' : Fin m → R)
    (Λ : Fin m → Fin m → Fin m → Fin m → R →+ M) :
    (∑ w, ∑ w', ∑ x, ∑ x', if w ≠ w' ∧ x ≠ x' then Λ (min w w') (max w w') (min x x') (max x x')
        (((sg2 w w' * sg2 x x' : ℤ) : R) * (β w * β' w' * (a x * a' x'))) else 0) =
      ∑ i, ∑ i', ∑ j, ∑ j', if i < i' ∧ j < j' then Λ i i' j j'
        ((-1) ^ (i.val + i'.val + j.val + j'.val) * (β i * β' i' - β i' * β' i) * (a j * a' j' - a j' * a' j))
        else 0 := by
  classical
  set T : Fin m → Fin m → Fin m → Fin m → M := fun w w' x x' => Λ (min w w') (max w w') (min x x') (max x x')
    (((sg2 w w' * sg2 x x' : ℤ) : R) * (β w * β' w' * (a x * a' x'))) with hT
  have hL : (∑ w, ∑ w', ∑ x, ∑ x', if w ≠ w' ∧ x ≠ x' then T w w' x x' else 0) =
      ∑ w, ∑ w', if w ≠ w' then ∑ x, ∑ x', (if x ≠ x' then T w w' x x' else 0) else 0 := by
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
    by_cases h : w = w'
    · simp [h]
    · simp [h]
  have hI : ∀ w w' : Fin m, (∑ x, ∑ x', if x ≠ x' then T w w' x x' else 0) =
      ∑ j, ∑ j', if j < j' then T w w' j j' + T w w' j' j else 0 := fun w w' => sg_pairs (T w w')
  rw [hL]
  simp_rw [hI]
  rw [sg_pairs (fun w w' => ∑ j, ∑ j', if j < j' then T w w' j j' + T w w' j' j else 0)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  by_cases hi : i < i'
  · rw [if_pos hi, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases hj : j < j'
    · rw [if_pos hj, if_pos hj, if_pos ⟨hi, hj⟩]
      obtain ⟨si1, si2⟩ := sign_pair_of_lt hi
      obtain ⟨sj1, sj2⟩ := sign_pair_of_lt hj
      simp only [hT, min_eq_left hi.le, max_eq_right hi.le, min_eq_right hi.le, max_eq_left hi.le,
        min_eq_left hj.le, max_eq_right hj.le, min_eq_right hj.le, max_eq_left hj.le, si1, si2, sj1, sj2]
      simp only [← map_add]
      congr 1
      push_cast
      ring
    · rw [if_neg hj, if_neg hj, if_neg (fun h => hj h.2)]
      simp
  · rw [if_neg hi]
    refine (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_).symm
    rw [if_neg (fun h => hi h.1)]

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section TB
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}

theorem stp_good_QL (ho : IsOpen (UU Dc)) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) :
    (sfData E L ho).Good (QL k r z z' L Y a b) :=
  sf_good_grp ho (Qx3.pres_tL z z' Y a b) (fun _ hc => Qx2.ll_tL (open_slice ho hc) z z' Y a b)

def tB (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (L : Fin (r + 1)) {Dc : (Fin r → ℂ) → Set (Mx k r)}
    (ho : IsOpen (UU Dc)) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) :
    Module.End ℂ (sfData E L ho).V := (sfData E L ho).hat (QL k r z z' L Y a b)

theorem capelli_block00_eq_full_minor (ho : IsOpen (UU Dc)) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) :
    tB E L ho z z' Y 0 0 = mB E L ho id id (uC k r L Y) := rfl

theorem stp_tB_apply (ho : IsOpen (UU Dc)) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2)
    (Ψ : (sfData E L ho).V) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r L) (hgD : g ∈ Dc c) :
    ((tB E L ho z z' Y a b Ψ : (sfData E L ho).V) : Fn k r E) c g = tL k r z z' L Y a b ((Ψ : Fn k r E) c) g :=
  sf_hat_apply ho (stp_good_QL ho z z' Y a b) Ψ hc hg hgD

theorem stp_mB_apply (ho : IsOpen (UU Dc)) {t : ℕ} (a b : Fin t → Fin (mdim k r L)) (u : ℂ)
    (Ψ : (sfData E L ho).V) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r L) (hgD : g ∈ Dc c) :
    ((mB E L ho a b u Ψ : (sfData E L ho).V) : Fn k r E) c g =
      qminorOp (EH k r) (posL k r L ∘ a) (posL k r L ∘ b) u ((Ψ : Fn k r E) c) g :=
  sf_hat_apply ho (good_mB ho a b u) Ψ hc hg hgD

def evP (ho : IsOpen (UU Dc)) (Ψ : (sfData E L ho).V) (c : Fin r → ℂ) (g : Mx k r) :
    Module.End ℂ (sfData E L ho).V →ₗ[ℂ] E where
  toFun := fun T => ((T Ψ : (sfData E L ho).V) : Fn k r E) c g
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem stp_end_ext (ho : IsOpen (UU Dc)) {T S : Module.End ℂ (sfData E L ho).V}
    (h : ∀ Ψ, ∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → evP ho Ψ c g T = evP ho Ψ c g S) : T = S :=
  LinearMap.ext fun Ψ => sf_ext ho (h Ψ)

theorem stp_ev_mul (ho : IsOpen (UU Dc)) {a : Fn k r ℂ} (ha : SmoothFam k r L (UU Dc) a) (Ψ : (sfData E L ho).V)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r L) (hgD : g ∈ Dc c)
    (T : Module.End ℂ (sfData E L ho).V) : evP ho Ψ c g (mulB E L ho a * T) = a c g • evP ho Ψ c g T :=
  mulB_apply ho ha (T Ψ) hc hg hgD

theorem signed_first_column_expansion_block01 (ho : IsOpen (UU Dc)) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) :
    (∑ w : Fin (mdim k r L), ∑ x : Fin (mdim k r L), (((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) * xv k r z' L x) •
      (mulB E L ho (aYb z L w) * mB E L ho (skip1 w) (skip1 x) (uC k r L Y - 1))) = -tB E L ho z z' Y 0 1 := by
  refine stp_end_ext ho (fun Ψ c hc g hg hgD => ?_)
  simp only [map_sum, map_smul, map_neg, stp_ev_mul ho (sf_aYb z _) Ψ hc hg hgD]
  show _ = -(((tB E L ho z z' Y 0 1 Ψ : (sfData E L ho).V) : Fn k r E) c g)
  rw [stp_tB_apply ho z z' Y 0 1 Ψ hc hg hgD]
  show _ = -(-(chatL (EH k r) (posL k r L) (uC k r L Y - 1) (fun _ => xv k r z' L) (ybv k r z L) ((Ψ : Fn k r E) c) g))
  rw [neg_neg]
  unfold chatL
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, ← stp_mB_apply ho _ _ _ Ψ hc hg hgD]
  congr 1
  simp only [aYb]
  push_cast
  ring

theorem signed_expansion_block10 (ho : IsOpen (UU Dc)) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) :
    (∑ w : Fin (mdim k r L), ∑ x : Fin (mdim k r L), (((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) * xbv k r z' L w) •
      (mulB E L ho (aY z L x) * mB E L ho (skip1 w) (skip1 x) (uC k r L Y))) = -tB E L ho z z' Y 1 0 := by
  refine stp_end_ext ho (fun Ψ c hc g hg hgD => ?_)
  simp only [map_sum, map_smul, map_neg, stp_ev_mul ho (sf_aY z _) Ψ hc hg hgD]
  show _ = -(((tB E L ho z z' Y 1 0 Ψ : (sfData E L ho).V) : Fn k r E) c g)
  rw [stp_tB_apply ho z z' Y 1 0 Ψ hc hg hgD]
  show _ = -(-(chatL (EH k r) (posL k r L) (uC k r L Y) (yv k r z L) (fun _ => xbv k r z' L) ((Ψ : Fn k r E) c) g))
  rw [neg_neg]
  unfold chatL
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, ← stp_mB_apply ho _ _ _ Ψ hc hg hgD]
  congr 1
  simp only [aY]
  push_cast
  ring

theorem signed_double_expansion_block11 (ho : IsOpen (UU Dc)) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) :
    (∑ w : Fin (mdim k r L), ∑ w' : Fin (mdim k r L), ∑ x : Fin (mdim k r L), ∑ x' : Fin (mdim k r L),
      if w ≠ w' ∧ x ≠ x' then (((sg2 w w' * sg2 x x' : ℤ) : ℂ) * (xv k r z' L x' * xbv k r z' L w')) •
        (mulB E L ho (aYb z L w) * (mulB E L ho (aY z L x) *
          mB E L ho (skip2 (min w w') (max w w')) (skip2 (min x x') (max x x')) (uC k r L Y - 1))) else 0) =
      -tB E L ho z z' Y 1 1 := by
  refine stp_end_ext ho (fun Ψ c hc g hg hgD => ?_)
  have key := double_sign_sum_reindex_ordered (R := ℂ) (M := E) (ybv k r z L g) (xbv k r z' L) (yv k r z L g) (xv k r z' L)
    (fun i i' j j' => (LinearMap.toSpanSingleton ℂ E (qminorOp (EH k r) (posL k r L ∘ skip2 i i')
      (posL k r L ∘ skip2 j j') (uC k r L Y - 1) ((Ψ : Fn k r E) c) g)).toAddMonoidHom)
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply] at key
  simp only [map_sum, map_neg, apply_ite (evP ho Ψ c g), map_zero, map_smul, stp_ev_mul ho (sf_aYb z _) Ψ hc hg hgD,
    stp_ev_mul ho (sf_aY z _) Ψ hc hg hgD]
  show _ = -(((tB E L ho z z' Y 1 1 Ψ : (sfData E L ho).V) : Fn k r E) c g)
  rw [stp_tB_apply ho z z' Y 1 1 Ψ hc hg hgD]
  show _ = -(-(chat2L (EH k r) (posL k r L) (uC k r L Y - 1) (yv k r z L) (fun _ => xv k r z' L) (ybv k r z L)
    (fun _ => xbv k r z' L) ((Ψ : Fn k r E) c) g))
  rw [neg_neg]
  unfold chat2L
  rw [← key]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun x' _ => ?_
  split_ifs
  · rw [smul_smul, smul_smul, ← stp_mB_apply ho _ _ _ Ψ hc hg hgD]
    congr 1
    simp only [aY, aYb]
    ring
  · rfl

end TB

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Alg
variable {B : Type*} [Ring B] [Algebra ℂ B] {m : ℕ}

theorem stp_sumA (A X : B) (ε : Fin m → Fin m → ℂ) (s : Fin m → Fin m → ℂ) (y : Fin m → Fin m → B) (M : Fin m → Fin m → B) :
    (∑ w, ∑ x, ε w x • (A * y w x * M w x * X * (s w x • (1 : B)))) =
      A * (∑ w, ∑ x, (ε w x * s w x) • (y w x * M w x)) * X := by
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, mul_assoc]

theorem stp_gauge (G P Pb C Ci Cb Cbi t00 t01 t10 t11 : B) (Y s : ℂ)
    (hP : P * G = G * (P + s • 1)) (hPb : Pb * G = G * (Pb + s • 1))
    (gC : Commute G C) (gCi : Commute G Ci) (gCb : Commute G Cb) (gCbi : Commute G Cbi)
    (g00 : Commute G t00) (g01 : Commute G t01) (g10 : Commute G t10) (g11 : Commute G t11)
    (c00 : Commute C t00) (c10 : Commute C t10) (ci01 : Commute Ci t01) (ci11 : Commute Ci t11)
    (cPb : Commute C Pb) (cCbi : Commute C Cbi) (cCb : Commute C Cb) (ciCbi : Commute Ci Cbi) :
    G * (((Y - s) • 1 - Pb) * t00 * ((Y + s) • 1 + P) + Cbi * t10 * ((Y + s) • 1 + P) +
        ((Y - s) • 1 - Pb) * Ci * t01 + Ci * Cbi * t11) =
      ((Y • 1 - Pb) * (t00 * (Y • 1 + P) + t01 * Ci) + Cbi * (t10 * (Y • 1 + P) + t11 * Ci)) * G ∧
    G * -(C * (((Y - s) • 1 - Pb) * t00 + Cbi * t10)) =
      ((Y • 1 - Pb) * (t00 * -C + t01 * 0) + Cbi * (t10 * -C + t11 * 0)) * G ∧
    G * -(Cb * (t00 * ((Y + s) • 1 + P) + Ci * t01)) =
      (-Cb * (t00 * (Y • 1 + P) + t01 * Ci) + 0 * (t10 * (Y • 1 + P) + t11 * Ci)) * G ∧
    G * (C * (Cb * t00)) = (-Cb * (t00 * -C + t01 * 0) + 0 * (t10 * -C + t11 * 0)) * G := by
  have a1 : G * ((Y + s) • 1 + P) = (Y • 1 + P) * G := by
    rw [add_mul, hP]
    simp only [mul_add, add_smul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    abel
  have a2 : G * ((Y - s) • 1 - Pb) = (Y • 1 - Pb) * G := by
    rw [sub_mul, hPb]
    simp only [mul_add, mul_sub, sub_smul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    abel
  have a3 : Commute C (Y • (1 : B) - Pb) := ((Commute.one_right C).smul_right Y).sub_right cPb
  generalize (Y + s) • (1 : B) + P = T1 at *
  generalize (Y - s) • (1 : B) - Pb = S1 at *
  generalize Y • (1 : B) + P = T0 at *
  generalize Y • (1 : B) - Pb = S0 at *
  have m : ∀ {X X' : B}, G * X = X' * G → ∀ Z : B, G * (X * Z) = X' * (G * Z) := fun h Z => by
    rw [← mul_assoc, h, mul_assoc]
  have n : ∀ {X X' : B}, Commute X X' → ∀ Z : B, X * (X' * Z) = X' * (X * Z) := fun h Z => by
    rw [← mul_assoc, h.eq, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mul_add, add_mul, mul_assoc, m a1, m a2, a1, m gCi.eq, m gCbi.eq, m g00.eq, m g10.eq,
      g01.eq, g11.eq, n ci01, n ci11, n ciCbi, gCi.eq]
    abel
  · simp only [mul_add, add_mul, mul_assoc, mul_neg, neg_mul, mul_zero, zero_mul, add_zero, m a2, m gC.eq,
      m gCbi.eq, g00.eq, g10.eq, n a3, n cCbi, n c00, n c10, neg_add]
  · simp only [mul_add, add_mul, mul_assoc, mul_neg, neg_mul, mul_zero, zero_mul, add_zero, a1, m gCb.eq,
      m gCi.eq, m g00.eq, g01.eq, n ci01, neg_add]
  · simp only [mul_add, add_mul, mul_assoc, mul_neg, neg_mul, mul_zero, zero_mul, add_zero, neg_neg, neg_zero, m gC.eq,
      m gCb.eq, g00.eq, n cCb, n c00]

end Alg

theorem stp_Mdim (l : Fin r) : ((Mdim k r l - 1 : ℕ) : ℂ) = (mdim k r l.succ : ℂ) + 1 := by
  have hl := l.isLt
  have h : Mdim k r l - 1 = mdim k r l.succ + 1 := by
    simp only [Mdim, mdim, Fin.val_succ]
    omega
  rw [h, Nat.cast_add, Nat.cast_one]

theorem stp_Mdim' (l : Fin r) : ((Mdim k r l : ℕ) : ℂ) = (mdim k r l.succ : ℂ) + 2 := by
  have hl := l.isLt
  have h : Mdim k r l = mdim k r l.succ + 2 := by
    simp only [Mdim, mdim, Fin.val_succ]
    omega
  rw [h, Nat.cast_add, Nat.cast_ofNat]

theorem stp_uC (l : Fin r) (Y : ℂ) : uC k r l.castSucc Y = Y + ((mdim k r l.succ : ℂ) + 1) / 2 := by
  simp only [uC]
  rw [mdim_eq k l]
  push_cast
  ring

theorem stp_uC_succ (l : Fin r) (Y : ℂ) : uC k r l.castSucc Y - 1 = uC k r l.succ Y := by
  simp only [uC]
  rw [mdim_eq k l]
  push_cast
  ring

theorem stp_uC_succ2 (l : Fin r) (Y : ℂ) : uC k r l.castSucc Y - 2 = uC k r l.succ Y - 1 := by
  simp only [uC]
  rw [mdim_eq k l]
  push_cast
  ring

section TForm
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {l : Fin r} {D : Set (Mx k r)}
  (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)

local notation "ho" => ho1 l hD
local notation "tt" => tB E l.succ (ho1 l hD) z z' Y
local notation "Ci" => mulB E l.succ (ho1 l hD) (aCi k l)
local notation "Cbi" => mulB E l.succ (ho1 l hD) (aCbi k l)
local notation "uu" => uC k r l.castSucc Y

theorem signed_sum_mulB_mB_eq_neg_tt_zero_one (A X : Module.End ℂ (sfData E l.succ ho).V) :
    (∑ w : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ), ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (A * mulB E l.succ ho (aYb z l.succ w) * mB E l.succ ho (skip1 w) (skip1 x) (uu - 2) * X *
        (xv k r z' l.succ x • 1))) = -(A * tt 0 1 * X) := by
  rw [stp_sumA A X (fun w x => ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ)) (fun _ x => xv k r z' l.succ x)
    (fun w _ => mulB E l.succ ho (aYb z l.succ w)) (fun w x => mB E l.succ ho (skip1 w) (skip1 x) (uu - 2)),
    stp_uC_succ2, signed_first_column_expansion_block01, mul_neg, neg_mul]

theorem signed_expansion_last_row_entry10 (A X : Module.End ℂ (sfData E l.succ ho).V) :
    (∑ w : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ), ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (A * mulB E l.succ ho (aY z l.succ x) * mB E l.succ ho (skip1 w) (skip1 x) (uu - 1) * X *
        (xbv k r z' l.succ w • 1))) = -(A * tt 1 0 * X) := by
  rw [stp_sumA A X (fun w x => ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ)) (fun w _ => xbv k r z' l.succ w)
    (fun _ x => mulB E l.succ ho (aY z l.succ x)) (fun w x => mB E l.succ ho (skip1 w) (skip1 x) (uu - 1)),
    stp_uC_succ, signed_expansion_block10, mul_neg, neg_mul]

theorem capelli_minor_two_removed_eq : doubleRemovedMinorTerm E l hD z z' uu = -(Ci * Cbi * tt 1 1) := by
  rw [← mul_neg, ← signed_double_expansion_block11, ← stp_uC_succ2]
  unfold doubleRemovedMinorTerm scaledRowVectorOperator scaledColumnVectorOperator
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun x' _ => ?_
  split_ifs
  · have h := (mulB_comm (E := E) ho (sf_aYb z w) (sf_aCbi l)).eq
    simp only [mul_smul_comm, smul_smul, mul_one, mul_assoc]
    rw [← mul_assoc (mulB E l.succ ho (aYb z l.succ w)) Cbi, h, mul_assoc]
  · exact (mul_zero _).symm

theorem bordered_first_column_expansion : bE1 E l hD z z' uu = tt 0 0 * bTee E l hD uu + Ci * tt 0 1 := by
  have h := signed_sum_mulB_mB_eq_neg_tt_zero_one (E := E) hD z z' Y Ci 1
  simp only [mul_one] at h
  unfold bE1 scaledRowVectorOperator
  rw [h, capelli_block00_eq_full_minor, stp_uC_succ, sub_neg_eq_add]

theorem bordered_last_column_expansion : borderedMinorLastColumn E l hD z z' (uu - 1) =
    bTss E l hD (uu - (mdim k r l.succ : ℂ) - 1) * tt 0 0 + Cbi * tt 1 0 := by
  have h := signed_expansion_last_row_entry10 (E := E) hD z z' Y Cbi 1
  simp only [mul_one] at h
  unfold borderedMinorLastColumn scaledColumnVectorOperator
  rw [h, capelli_block00_eq_full_minor, sub_right_comm uu 1, stp_uC_succ, sub_neg_eq_add]

theorem capelli_second_order_expansion : capelliDetSecondFactorOrder E l hD z z' uu =
    bTss E l hD (uu - (mdim k r l.succ : ℂ) - 1) * tt 0 0 * bTee E l hD uu + Cbi * tt 1 0 * bTee E l hD uu +
      bTss E l hD (uu - (mdim k r l.succ : ℂ) - 1) * Ci * tt 0 1 + Ci * Cbi * tt 1 1 := by
  have h1 := signed_expansion_last_row_entry10 (E := E) hD z z' Y Cbi (bTee E l hD uu)
  have h2 := signed_sum_mulB_mB_eq_neg_tt_zero_one (E := E) hD z z' Y (bTss E l hD (uu - (mdim k r l.succ : ℂ) - 1) * Ci) 1
  simp only [mul_one] at h2
  unfold capelliDetSecondFactorOrder scaledRowVectorOperator scaledColumnVectorOperator
  simp only [← mul_assoc]
  rw [h1, h2, capelli_minor_two_removed_eq, capelli_block00_eq_full_minor, stp_uC_succ, sub_neg_eq_add, sub_neg_eq_add, sub_neg_eq_add]

theorem stp_P_comm {a : Fn k r ℂ} (ha : SmoothFam k r l.succ (UU (Dc1 l D)) a)
    (h : ∀ c ∈ OmX r, ∀ g, pOp l (fun c' => a c' g) c = 0) (u : ℂ) :
    Commute (mulB E l.succ ho a) (bTee E l hD u) := by
  have := P_mulB_of (E := E) ho l ha 0 (fun c hc g => by rw [h c hc g, zero_mul])
  rw [zero_smul, add_zero] at this
  exact ((Commute.one_right _).smul_right u).add_right this.symm

theorem capelli_first_order_expansion : capelliDetFirstFactorOrder E l hD z z' uu =
    bTee E l hD uu * tt 0 0 * bTss E l hD (uu - (mdim k r l.succ : ℂ) - 1) + bTee E l hD uu * Cbi * tt 1 0 +
      Ci * tt 0 1 * bTss E l hD (uu - (mdim k r l.succ : ℂ) - 1) + Ci * Cbi * tt 1 1 := by
  have h1 := signed_expansion_last_row_entry10 (E := E) hD z z' Y (bTee E l hD uu * Cbi) 1
  have h2 := signed_sum_mulB_mB_eq_neg_tt_zero_one (E := E) hD z z' Y Ci (bTss E l hD (uu - (mdim k r l.succ : ℂ) - 1))
  have h3 : ∀ x, Cbi * mulB E l.succ ho (aY z l.succ x) * bTee E l hD uu =
      bTee E l hD uu * Cbi * mulB E l.succ ho (aY z l.succ x) := fun x => by
    rw [mul_assoc (bTee E l hD uu)]
    exact ((stp_P_comm hD (sf_aCbi l) (fun c hc _ => pOp_cbi l hc) uu).mul_left
      (stp_P_comm hD (sf_aY z x) (fun c _ _ => pOp_const l _ c) uu)).eq
  simp only [mul_one] at h1
  unfold capelliDetFirstFactorOrder scaledRowVectorOperator scaledColumnVectorOperator
  simp only [h3]
  rw [h1, h2, capelli_minor_two_removed_eq, capelli_block00_eq_full_minor, stp_uC_succ, sub_neg_eq_add, sub_neg_eq_add, sub_neg_eq_add]

end TForm

end Formalism.FourierDecayAlt.P.Qx6

end

section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.Qx6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Fin
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ} {l : Fin r}
  {D : Set (Mx k r)}

theorem stp_rep_ev {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)} (ho : IsOpen (UU Dc))
    {T : Fn k r E → Fn k r E} {b : Module.End ℂ (sfData E L ho).V} (h : HatData.Rep (sfData E L ho) T b)
    {Φ : Fn k r E} (hΦ : SmoothFam k r L (UU Dc) Φ) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r}
    (hg : g ∈ Glev k r L) (hgD : g ∈ Dc c) : T Φ c g = evP ho ((sfData E L ho).toV Φ hΦ) c g b := by
  have h1 := congrFun (congrFun (h.apply (x := Φ) hΦ) c) g
  exact (cutP_on (T Φ) hc hg hgD).symm.trans h1

theorem stp_toV_rr (hW : WeylLevelElementFacts) (hD : IsOpen D) {J : Mx k r → E} (hJ : SmoothLev k r l.castSucc D J) :
    (sfData E l.succ (ho1 l hD)).toV (rr l J) (sf_rr hW l hJ) = rho E hW l hD (J0 hD hJ) := by
  refine sf_ext _ (fun c hc g hg hgD => ?_)
  rw [rho_apply hW l hD _ hc hg hgD, restricted_function_on_level hD hJ (pt_mem hW l hc hg hgD)]
  exact cutP_on (rr l J) hc hg hgD

theorem restriction_to_next_level_smooth (hW : WeylLevelElementFacts) {J : Mx k r → E} (hJ : SmoothLev k r l.castSucc D J) :
    SmoothFam k r l.succ (UU (Dc1 l D)) (res1 k r l J) := Qx3.sf_smul (sf_aG l) (sf_rr hW l hJ)

theorem restriction_to_vector_space_eq (hW : WeylLevelElementFacts) (hD : IsOpen D) {J : Mx k r → E} (hJ : SmoothLev k r l.castSucc D J) :
    (sfData E l.succ (ho1 l hD)).toV (res1 k r l J) (restriction_to_next_level_smooth hW hJ) =
      mulB E l.succ (ho1 l hD) (aG k l) (rho E hW l hD (J0 hD hJ)) := by
  refine sf_ext _ (fun c hc g hg hgD => ?_)
  rw [mulB_apply _ (sf_aG l) _ hc hg hgD, rho_apply hW l hD _ hc hg hgD, restricted_function_on_level hD hJ (pt_mem hW l hc hg hgD)]
  exact cutP_on (res1 k r l J) hc hg hgD

theorem stp_evalPt (hW : WeylLevelElementFacts) (hD : IsOpen D) {J : Mx k r → E} (hJ : SmoothLev k r l.castSucc D J)
    {VL : Submodule ℂ (levData E l.castSucc hD).V} {t : ℕ} {a b : Fin t → Fin (mdim k r l.castSucc)} {u : ℂ}
    {T' : Module.End ℂ (sfData E l.succ (ho1 l hD)).V}
    (h : IntJ (rho E hW l hD) VL (J0 hD hJ) (qminor (E0 E l.castSucc hD) a b u) T')
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r l.succ) (hgD : g ∈ Dc1 l D c) :
    qminorOp (EH k r) (posL k r l.castSucc ∘ a) (posL k r l.castSucc ∘ b) u J (w1 k r l (c l) * g) =
      evP (ho1 l hD) (rho E hW l hD (J0 hD hJ)) c g T' := by
  show _ = ((T' (rho E hW l hD (J0 hD hJ)) : (sfData E l.succ (ho1 l hD)).V) : Fn k r E) c g
  rw [← h.2, rho_apply hW l hD _ hc hg hgD, quantum_minor_level_eq_hat]
  unfold J0
  rw [HatData.hat_toV (good_qm hD a b u) hJ]
  exact (level_restriction_apply_on _ (pt_mem hW l hc hg hgD)).symm

theorem stp_q_id (hD : IsOpen D) (u : ℂ) : qminor (E0 E l.castSucc hD) id id u =
    qminor (E0 E l.castSucc hD) (bE (e0 k l) (bS (v0 k l) (es0 k l))) (bE (e0 k l) (bS (v0 k l) (es0 k l))) u := by
  rw [id_eq_b k l, qminor_cast]

theorem stp_q_e (hD : IsOpen D) (u : ℂ) : qminor (E0 E l.castSucc hD) (skip1 (e0 k l)) (skip1 (e0 k l)) u =
    qminor (E0 E l.castSucc hD) (bS (v0 k l) (es0 k l)) (bS (v0 k l) (es0 k l)) u := by
  rw [skip_first_basis_eq_embedding k l, qminor_cast]

theorem stp_q_es (hD : IsOpen D) (u : ℂ) : qminor (E0 E l.castSucc hD) (skip1 (es0 k l)) (skip1 (es0 k l)) u =
    qminor (E0 E l.castSucc hD) (bE (e0 k l) (v0 k l)) (bE (e0 k l) (v0 k l)) u := by
  rw [skip_last_basis_eq_embedding k l, qminor_cast]

theorem stp_q_ees (hD : IsOpen D) (u : ℂ) :
    qminor (E0 E l.castSucc hD) (skip2 (e0 k l) (es0 k l)) (skip2 (e0 k l) (es0 k l)) u =
      qminor (E0 E l.castSucc hD) (v0 k l) (v0 k l) u := by
  rw [double_skip_first_last_basis k l, qminor_cast]

theorem stp_repT (hD : IsOpen D) (u : ℂ) :
    HatData.Rep (sfData E l.succ (ho1 l hD)) (fun Ψ => u • Ψ + crd (pOp l) Ψ) (bTee E l hD u) :=
  (HatData.rep_id.smul u).add (⟨sf_good_crd _ l 0, rfl⟩ : HatData.Rep _ (crd (opL l 0)) _)

theorem stp_repS (hD : IsOpen D) (u : ℂ) :
    HatData.Rep (sfData E l.succ (ho1 l hD)) (fun Ψ => u • Ψ - crd (pbOp l) Ψ) (bTss E l hD u) :=
  (HatData.rep_id.smul u).sub (⟨sf_good_crd _ l 3, rfl⟩ : HatData.Rep _ (crd (opL l 3)) _)

theorem stp_repM (hD : IsOpen D) {a : Fn k r ℂ} (ha : SmoothFam k r l.succ (UU (Dc1 l D)) a) :
    HatData.Rep (sfData E l.succ (ho1 l hD)) (mulF a) (mulB E l.succ (ho1 l hD) a) := ⟨sf_good_mul _ ha, rfl⟩

theorem stp_repQ (hD : IsOpen D) (Y : ℂ) (a b : Fin 2) :
    HatData.Rep (sfData E l.succ (ho1 l hD)) (QL k r z z' l.succ Y a b) (tB E l.succ (ho1 l hD) z z' Y a b) :=
  ⟨stp_good_QL _ z z' Y a b, rfl⟩

theorem stp_repTL (hD : IsOpen D) (Y : ℂ) (a b : Fin 2) :
    HatData.Rep (sfData E l.succ (ho1 l hD)) (TL k l Y a b)
      (!![bTee E l hD Y, -mulB E l.succ (ho1 l hD) (aC k l); mulB E l.succ (ho1 l hD) (aCi k l), 0] a b) := by
  fin_cases a <;> fin_cases b
  · exact stp_repT hD Y
  · exact (stp_repM hD (sf_aC l)).neg
  · exact stp_repM hD (sf_aCi l)
  · exact HatData.rep_zero

theorem stp_repTLs (hD : IsOpen D) (Y : ℂ) (a b : Fin 2) :
    HatData.Rep (sfData E l.succ (ho1 l hD)) (TLs k l Y a b)
      (!![bTss E l hD Y, mulB E l.succ (ho1 l hD) (aCbi k l); -mulB E l.succ (ho1 l hD) (aCb k l), 0] a b) := by
  fin_cases a <;> fin_cases b
  · exact stp_repS hD Y
  · exact stp_repM hD (sf_aCbi l)
  · exact (stp_repM hD (sf_aCb l)).neg
  · exact HatData.rep_zero

theorem stp_rep_oMul {X : Type*} [AddCommGroup X] [Module ℂ X] {H : HatData X} {M N : OM X}
    {M' N' : Fin 2 → Fin 2 → Module.End ℂ H.V} (hM : ∀ a b, HatData.Rep H (M a b) (M' a b))
    (hN : ∀ a b, HatData.Rep H (N a b) (N' a b)) (a b : Fin 2) :
    HatData.Rep H (oMul M N a b) (M' a 0 * N' 0 b + M' a 1 * N' 1 b) := by
  rw [oMul_eq]
  exact ((hM a 0).comp (hN 0 b)).add ((hM a 1).comp (hN 1 b))

theorem stp_tB_comm (hD : IsOpen D) (Y : ℂ) (a b : Fin 2) {α : (Fin r → ℂ) → ℂ}
    (hα : SmoothFam k r l.succ (UU (Dc1 l D)) (fun c _ => α c)) :
    Commute (mulB E l.succ (ho1 l hD) (fun c _ => α c)) (tB E l.succ (ho1 l hD) z z' Y a b) :=
  mulB_grp_comm _ hα (Qx3.pres_tL z z' Y a b) (fun _ hc => Qx2.ll_tL (open_slice (ho1 l hD) hc) z z' Y a b)

end Fin

theorem stp_chainStepRaw (R : Rules) (hB : BorderFull) : ChainStepRaw := by
  intro Wp Wq _ _ _ _ k r z z' π π' l D Y hz hz' hD J hJ c hc g hg hgD
  obtain ⟨hs, hl, hr, -⟩ := hJ
  have h1 := capelli_det_first_order_intertwines R hz hz' hD hs hl hr hB (uC k r l.castSucc Y)
  rw [← stp_q_id, capelli_first_order_expansion] at h1
  have h2 := stp_evalPt R.w hD.1 hs h1 hc hg hgD
  have e : uC k r l.castSucc Y - (Mdim k r l : ℂ) + 1 = uC k r l.castSucc Y - (mdim k r l.succ : ℂ) - 1 := by
    rw [stp_Mdim']
    ring
  have rP := stp_repT (E := Wq →L[ℂ] Wp) (l := l) hD.1 (uC k r l.castSucc Y)
  have rM := stp_repS (E := Wq →L[ℂ] Wp) (l := l) hD.1 (uC k r l.castSucc Y - (mdim k r l.succ : ℂ) - 1)
  have rQ := stp_repQ (E := Wq →L[ℂ] Wp) (l := l) (z := z) (z' := z') hD.1 Y
  have rI := stp_repM (E := Wq →L[ℂ] Wp) (l := l) hD.1 (sf_aCi l)
  have rJ := stp_repM (E := Wq →L[ℂ] Wp) (l := l) hD.1 (sf_aCbi l)
  have rr' := (((rP.comp ((rQ 0 0).comp rM)).add (rP.comp (rJ.comp (rQ 1 0)))).add
    (rI.comp ((rQ 0 1).comp rM))).add (rI.comp (rJ.comp (rQ 1 1)))
  have h3 := stp_rep_ev (ho1 l hD.1) rr' (sf_rr R.w l hs) hc hg hgD
  rw [stp_toV_rr R.w hD.1 hs] at h3
  simp only [← mul_assoc] at h3
  intro Φ u Pp Pm
  simp only [Pm, u, e]
  exact h2.trans h3.symm

section Keys
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {l : Fin r} {D : Set (Mx k r)}
  (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)

local notation "tt" => tB E l.succ (ho1 l hD) z z' Y
local notation "mm" => mulB E l.succ (ho1 l hD)
local notation "uu" => uC k r l.castSucc Y

theorem stp_keys :
    mm (aG k l) * capelliDetSecondFactorOrder E l hD z z' uu =
      (bTss E l hD Y * (tt 0 0 * bTee E l hD Y + tt 0 1 * mm (aCi k l)) +
        mm (aCbi k l) * (tt 1 0 * bTee E l hD Y + tt 1 1 * mm (aCi k l))) * mm (aG k l) ∧
    mm (aG k l) * -(mm (aC k l) * borderedMinorLastColumn E l hD z z' (uu - 1)) =
      (bTss E l hD Y * (tt 0 0 * -mm (aC k l) + tt 0 1 * 0) +
        mm (aCbi k l) * (tt 1 0 * -mm (aC k l) + tt 1 1 * 0)) * mm (aG k l) ∧
    mm (aG k l) * -(mm (aCb k l) * bE1 E l hD z z' uu) =
      (-mm (aCb k l) * (tt 0 0 * bTee E l hD Y + tt 0 1 * mm (aCi k l)) +
        0 * (tt 1 0 * bTee E l hD Y + tt 1 1 * mm (aCi k l))) * mm (aG k l) ∧
    mm (aG k l) * (mm (aC k l) * (mm (aCb k l) * mB E l.succ (ho1 l hD) id id (uu - 1))) =
      (-mm (aCb k l) * (tt 0 0 * -mm (aC k l) + tt 0 1 * 0) +
        0 * (tt 1 0 * -mm (aC k l) + tt 1 1 * 0)) * mm (aG k l) := by
  have eP : uu = Y + ((mdim k r l.succ : ℂ) + 1) / 2 := stp_uC l Y
  have eM : uu - (mdim k r l.succ : ℂ) - 1 = Y - ((mdim k r l.succ : ℂ) + 1) / 2 := by
    rw [eP]
    ring
  have gP := P_mulB_of (E := E) (ho1 l hD) l (sf_aG (L := l.succ) l) (((mdim k r l.succ : ℂ) + 1) / 2)
    (fun c hc _ => by
      rw [← stp_Mdim l]
      exact pOp_gamma l hc _)
  have gPb := Pb_mulB_of (E := E) (ho1 l hD) l (sf_aG (L := l.succ) l) (((mdim k r l.succ : ℂ) + 1) / 2)
    (fun c hc _ => by
      rw [← stp_Mdim l]
      exact pbOp_gamma l hc _)
  have cPb := Pb_mulB_of (E := E) (ho1 l hD) l (sf_aC (L := l.succ) l) 0 (fun c hc _ => by
    rw [zero_mul]
    exact pbOp_coord l hc)
  rw [zero_smul, add_zero] at cPb
  have mc := fun {a a' : Fn k r ℂ} ha ha' => mulB_comm (E := E) (L := l.succ) (a := a) (a' := a') (ho1 l hD) ha ha'
  have tG : ∀ a b, Commute (mm (aG k l)) (tt a b) := fun a b =>
    stp_tB_comm hD Y a b (α := fun c => ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ)) (sf_aG l)
  have tC : ∀ a b, Commute (mm (aC k l)) (tt a b) := fun a b => stp_tB_comm hD Y a b (α := fun c => c l) (sf_aC l)
  have tI : ∀ a b, Commute (mm (aCi k l)) (tt a b) := fun a b =>
    stp_tB_comm hD Y a b (α := fun c => (c l)⁻¹) (sf_aCi l)
  rw [capelli_second_order_expansion, bordered_last_column_expansion, bordered_first_column_expansion, stp_uC_succ, ← capelli_block00_eq_full_minor (ho1 l hD) z z' Y, eM, eP]
  exact stp_gauge _ _ _ _ _ _ _ _ _ _ _ Y _ gP gPb
    (mc (sf_aG l) (sf_aC l)) (mc (sf_aG l) (sf_aCi l)) (mc (sf_aG l) (sf_aCb l)) (mc (sf_aG l) (sf_aCbi l))
    (tG 0 0) (tG 0 1) (tG 1 0) (tG 1 1) (tC 0 0) (tC 1 0) (tI 0 1) (tI 1 1)
    cPb.symm (mc (sf_aC l) (sf_aCbi l)) (mc (sf_aC l) (sf_aCb l)) (mc (sf_aCi l) (sf_aCbi l))

theorem stp_fin {X X' : Module.End ℂ (sfData E l.succ (ho1 l hD)).V} (h : mm (aG k l) * X = X' * mm (aG k l))
    (Ψ : (sfData E l.succ (ho1 l hD)).V) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r l.succ)
    (hgD : g ∈ Dc1 l D c) {v : E} (hv : v = evP (ho1 l hD) Ψ c g X) :
    aG k l c g • v = evP (ho1 l hD) (mm (aG k l) Ψ) c g X' := by
  rw [hv, ← stp_ev_mul (ho1 l hD) (sf_aG l) Ψ hc hg hgD, h]
  rfl

end Keys

section Entries
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ} {l : Fin r}
  {D : Set (Mx k r)} (R : Rules) (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' l.castSucc D)
  {J : Mx k r → E} (hs : SmoothLev k r l.castSucc D J) (hl : LeftEq k r z l.castSucc D J)
  (hr : RightEq k r z' l.castSucc D J) (Y : ℂ) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r}
  (hg : g ∈ Glev k r l.succ) (hgD : g ∈ Dc1 l D c)

local notation "mm" => mulB E l.succ (ho1 l (And.left hD))
local notation "uu" => uC k r l.castSucc Y
local notation "ev" => evP (ho1 l (And.left hD)) (rho E (Rules.w R) l (And.left hD) (J0 (And.left hD) hs)) c g

include hz hz' hl hr hc hg hgD in
theorem tL_zero_zero_w1_mul_eq_capelliDet (hB : BorderFull) :
    tL k r z z' l.castSucc Y 0 0 J (w1 k r l (c l) * g) = ev (capelliDetSecondFactorOrder E l hD.1 z z' uu) := by
  have h1 := capelli_det_second_order_intertwines R hz hz' hD hs hl hr hB uu
  rw [← stp_q_id] at h1
  exact stp_evalPt R.w hD.1 hs h1 hc hg hgD

include hz hz' hl hr hc hg hgD in
theorem tL_zero_one_w1_mul_eq_neg_borderedMinor (hS : BorderS) :
    tL k r z z' l.castSucc Y 0 1 J (w1 k r l (c l) * g) = ev (-(mm (aC k l) * borderedMinorLastColumn E l hD.1 z z' (uu - 1))) := by
  have h1 := evalS R hz hz' hD hs hl hr hS (uu - 1)
  rw [← stp_q_e] at h1
  rw [(tL_cell z z' l Y J (hc l) hg).1, stp_evalPt R.w hD.1 hs h1 hc hg hgD, map_neg,
    stp_ev_mul _ (sf_aC l) _ hc hg hgD]
  rfl

include hz hz' hl hr hc hg hgD in
theorem tL_one_zero_w1_mul_eq_neg_bE1 (hE : BorderE) :
    tL k r z z' l.castSucc Y 1 0 J (w1 k r l (c l) * g) = ev (-(mm (aCb k l) * bE1 E l hD.1 z z' uu)) := by
  have h1 := evalE R hz hz' hD hs hl hr hE uu
  rw [← stp_q_es] at h1
  rw [(tL_cell z z' l Y J (hc l) hg).2.1, stp_evalPt R.w hD.1 hs h1 hc hg hgD, map_neg,
    stp_ev_mul _ (sf_aCb l) _ hc hg hgD]
  rfl

include hl hc hg hgD in
theorem tL_one_one_w1_mul_eq_mB : tL k r z z' l.castSucc Y 1 1 J (w1 k r l (c l) * g) =
    ev (mm (aC k l) * (mm (aCb k l) * mB E l.succ (ho1 l hD.1) id id (uu - 1))) := by
  have h1 := (int_C R.w R.ep R.q hD (uu - 1)).toJ (restricted_function_mem_left_space hD hs hl)
  rw [← stp_q_ees] at h1
  rw [(tL_cell z z' l Y J (hc l) hg).2.2, stp_evalPt R.w hD.1 hs h1 hc hg hgD,
    stp_ev_mul _ (sf_aC l) _ hc hg hgD, stp_ev_mul _ (sf_aCb l) _ hc hg hgD, smul_smul]
  rfl

end Entries

theorem stp_chainStep (R : Rules) (hE : BorderE) (hS : BorderS) (hB : BorderFull) : ChainStep := by
  intro Wp Wq _ _ _ _ k r z z' π π' l D Y a b hz hz' hD J hJ c hc g hg hgD
  obtain ⟨hs, hl, hr, -⟩ := hJ
  have hgD' : g ∈ Dc1 l D c := hgD
  have rR := stp_rep_oMul (stp_repTLs (E := Wq →L[ℂ] Wp) (l := l) hD.1 Y)
    (stp_rep_oMul (stp_repQ (z := z) (z' := z') hD.1 Y) (stp_repTL hD.1 Y)) a b
  rw [stp_rep_ev (ho1 l hD.1) rR (restriction_to_next_level_smooth R.w hs) hc hg hgD', restriction_to_vector_space_eq R.w hD.1 hs]
  obtain ⟨k00, k01, k10, k11⟩ := stp_keys (E := Wq →L[ℂ] Wp) (l := l) hD.1 z z' Y
  fin_cases a <;> fin_cases b
  · exact stp_fin hD.1 k00 _ hc hg hgD' (tL_zero_zero_w1_mul_eq_capelliDet R hz hz' hD hs hl hr Y hc hg hgD' hB)
  · exact stp_fin hD.1 k01 _ hc hg hgD' (tL_zero_one_w1_mul_eq_neg_borderedMinor R hz hz' hD hs hl hr Y hc hg hgD' hS)
  · exact stp_fin hD.1 k10 _ hc hg hgD' (tL_one_zero_w1_mul_eq_neg_bE1 R hz hz' hD hs hl hr Y hc hg hgD' hE)
  · exact stp_fin hD.1 k11 _ hc hg hgD' (tL_one_one_w1_mul_eq_mB R hD hs hl Y hc hg hgD')

theorem stp_chainStepFromRules : ChainStepFromRules := fun hE hS hB gl ep q rr rl rt w =>
  ⟨stp_chainStepRaw ⟨gl, ep, q, rr, rl, rt, w⟩ hB, stp_chainStep ⟨gl, ep, q, rr, rl, rt, w⟩ hE hS hB⟩

end Formalism.FourierDecayAlt.P.Qx6

end

namespace Formalism.FourierDecayAlt.P

theorem chain_descent_from_rules : Formalism.FourierDecayAlt.Q.ChainStepFromRules := Qx6.stp_chainStepFromRules

theorem qx_chainStepBoth : Formalism.FourierDecayAlt.Q.ChainStepRaw ∧ Formalism.FourierDecayAlt.Q.ChainStep :=
  chain_descent_from_rules border_first_expansion border_last_expansion border_full_expansion generator_gl_level
    generator_action_preserved quantum_minor_left_hermitian right_action_rule left_action_rule torus_action_rule weyl_level_element_properties

theorem chain_descent_relation_raw : Formalism.FourierDecayAlt.Q.ChainStepRaw := qx_chainStepBoth.1

theorem chain_descent_relation : Formalism.FourierDecayAlt.Q.ChainStep := qx_chainStepBoth.2

theorem qx_chainAllBoth : Formalism.FourierDecayAlt.Q.ChainAll ∧ Formalism.FourierDecayAlt.Q.CVv :=
  chain_recursion_from_single_descent chain_descent_relation restriction_mem restriction_good_family family_operators
    operator_preserves_fusion_forms transfer_linear_local weyl_level_element_properties

theorem chain_recursion_all_levels : Formalism.FourierDecayAlt.Q.ChainAll := qx_chainAllBoth.1

theorem capelli_vector_valued_all_levels : Formalism.FourierDecayAlt.Q.CVv := qx_chainAllBoth.2

end Formalism.FourierDecayAlt.P

end
