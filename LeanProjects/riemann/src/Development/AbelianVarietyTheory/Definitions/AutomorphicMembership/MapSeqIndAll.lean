import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ClosureImageSpan

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def castV {A B : HLat K} (h : A = B) : A.V ≃ₗ[K] B.V := by
  subst h
  exact LinearEquiv.refl K A.V

def unitLat (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) : HLat K :=
  HLat.ofCoord (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))) fun _ => 1

theorem ofCoord_good {d : ℕ} {L : Submodule (𝓞 K) (Fin d → K)} {X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ}
    (hL : Submodule.IsLattice K L) (hX : ∀ v, IsUnit (X v).det) : (HLat.ofCoord L X).Good :=
  ⟨hX, hL.fg, hL.span_eq_top⟩

theorem unitLat_good (n : ℕ) : (unitLat K n).Good :=
  ⟨fun _ => by
      show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
      rw [Matrix.det_one]; exact isUnit_one,
    Submodule.fg_span (Set.finite_range _),
    (Submodule.span_span_of_tower (𝓞 K) K (Set.range (Pi.basisFun K (Fin n)))).trans (Pi.basisFun K (Fin n)).span_eq⟩

def unitMap (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    (unitLat K (Module.finrank ℂ W)).V →ₛₗ[σ] W :=
  (lin (stdOrthonormalBasis ℂ W)).comp (cptL σ (Module.finrank ℂ W))

theorem unitMap_b (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (k : Fin (Module.finrank ℂ W)) :
    unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k) = stdOrthonormalBasis ℂ W k := by
  have h : cptL σ (Module.finrank ℂ W) (Pi.basisFun K _ k) = Pi.single k 1 := by
    funext i
    by_cases hi : i = k <;> simp [cptL, cpt, hi]
  exact (congrArg (lin (stdOrthonormalBasis ℂ W)) h).trans (lin_single _ k)

theorem unitMap_basis (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    LinearIndependent ℂ (fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) ∧
      Submodule.span ℂ (Set.range fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) = ⊤ := by
  have h : (fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) = (stdOrthonormalBasis ℂ W).toBasis :=
    funext fun k => unitMap_b σ W k
  rw [h]
  exact ⟨(stdOrthonormalBasis ℂ W).toBasis.linearIndependent, (stdOrthonormalBasis ℂ W).toBasis.span_eq⟩

theorem hLatTie_castV {d : ℕ} {L : Submodule (𝓞 K) (Fin d → K)} {X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ} {A : HLat K}
    (h : HLat.ofCoord L X = A) : HLatTie A L X (castV h) := by
  subst h
  exact ⟨(Submodule.map_id L).symm, fun _ _ _ => rfl⟩

variable {m : ℕ} {d : Fin m → ℕ} (M : ∀ i, Submodule (𝓞 K) (Fin (d i) → K))
  (X : ∀ i, InfinitePlace K → Matrix (Fin (d i)) (Fin (d i)) ℂ)
  (W : ℕ → Type) [∀ j, NormedAddCommGroup (W j)] [∀ j, InnerProductSpace ℂ (W j)] [∀ j, FiniteDimensional ℂ (W j)]

def latSeq : ℕ → HLat K
  | 0 => unitLat K (Module.finrank ℂ (W 0))
  | j + 1 => if h : j < m then HLat.ofCoord (M ⟨j, h⟩) (X ⟨j, h⟩) else unitLat K (Module.finrank ℂ (W (j + 1)))

theorem latSeq_succ (i : Fin m) : latSeq M X W ((i : ℕ) + 1) = HLat.ofCoord (M i) (X i) := dif_pos i.2

theorem latSeq_off {j : ℕ} (h : j = 0 ∨ m < j) : latSeq M X W j = unitLat K (Module.finrank ℂ (W j)) := by
  cases j with
  | zero => rfl
  | succ j => exact dif_neg (by omega)

variable {σ : K →+* ℂ} (f : ∀ i : Fin m, (Fin (d i) → K) →ₛₗ[σ] W ((i : ℕ) + 1))

def mapSeq : ∀ j, (latSeq M X W j).V →ₛₗ[σ] W j
  | 0 => unitMap σ (W 0)
  | j + 1 =>
    if h : j < m then (f ⟨j, h⟩).comp (castV (latSeq_succ M X W ⟨j, h⟩)).toLinearMap
    else (unitMap σ (W (j + 1))).comp (castV (latSeq_off M X W (Or.inr (Nat.lt_succ_of_le (Nat.le_of_not_lt h))))).toLinearMap

theorem mapSeq_succ (i : Fin m) :
    mapSeq M X W f ((i : ℕ) + 1) = (f i).comp (castV (latSeq_succ M X W i)).toLinearMap := dif_pos i.2

theorem mapSeq_off {j : ℕ} (h : j = 0 ∨ m < j) :
    mapSeq M X W f j = (unitMap σ (W j)).comp (castV (latSeq_off M X W h)).toLinearMap := by
  cases j with
  | zero => rfl
  | succ j => exact dif_neg (by omega)

theorem castV_ind {H : Type} [AddCommGroup H] [Module ℂ H] (P : ∀ A : HLat K, (A.V →ₛₗ[σ] H) → Prop) {A B : HLat K} (h : A = B)
    {g : B.V →ₛₗ[σ] H} (hg : P B g) : P A (g.comp (castV h).toLinearMap) := by
  subst h
  exact hg

theorem mapSeq_ind (P : ∀ (j : ℕ) (A : HLat K), (A.V →ₛₗ[σ] W j) → Prop)
    (hP : ∀ i : Fin m, P ((i : ℕ) + 1) (HLat.ofCoord (M i) (X i)) (f i)) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ m) :
    P j (latSeq M X W j) (mapSeq M X W f j) := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [mapSeq_succ]
  exact castV_ind (P _) _ (hP i)

theorem mapSeq_ind_all (P : ∀ (j : ℕ) (A : HLat K), (A.V →ₛₗ[σ] W j) → Prop)
    (hP : ∀ i : Fin m, P ((i : ℕ) + 1) (HLat.ofCoord (M i) (X i)) (f i))
    (h0 : ∀ j, P j (unitLat K (Module.finrank ℂ (W j))) (unitMap σ (W j))) (j : ℕ) :
    P j (latSeq M X W j) (mapSeq M X W f j) := by
  by_cases h : j = 0 ∨ m < j
  · rw [mapSeq_off M X W f h]
    exact castV_ind (P _) _ (h0 j)
  · exact mapSeq_ind M X W f P hP j (by omega) (by omega)

theorem map_castV {H : ℕ → HLat K} {g : ∀ j, (H j).V →ₛₗ[σ] W j} (hH : H = latSeq M X W) (hg : HEq g (mapSeq M X W f))
    (i : Fin m) (h : HLat.ofCoord (M i) (X i) = H ((i : ℕ) + 1)) (x : Fin (d i) → K) :
    g ((i : ℕ) + 1) (castV h x) = f i x := by
  subst hH
  obtain rfl := eq_of_heq hg
  rw [mapSeq_succ]
  have key : ∀ {A B : HLat K} (h : A = B) (h' : B = A) (y : A.V), castV h' (castV h y) = y := by
    intro A B h h' y
    subst h
    rfl
  exact congrArg (f i) (key h _ x)

end Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

open MjCoord

def mjLat (R : RealDat3 D A3 Ks) (F : Face3 D A3) : ℕ → HLat D.what₂.LL :=
  latSeq (m := D.R.m) (d := fun i => (s0Of R F).dW i) (fun i => (s0Of R F).M i) (fun i => (s0Of R F).XW i) D.what₂.Mj

def mjH (_Z : ReadL R F X0 Y) (j : ℕ) : HLat D.what₂.LL := mjLat R F j

def jM (Z : ReadL R F X0 Y) (j : ℕ) : (mjH Z j).V →ₛₗ[D.what₂.embLL] D.what₂.Mj j :=
  mapSeq (m := D.R.m) (d := fun i => (s0Of R F).dW i) (fun i => (s0Of R F).M i) (fun i => (s0Of R F).XW i) D.what₂.Mj Z.jW j

variable (Z : ReadL R F X0 Y)

theorem mjH_succ (i : Fin D.R.m) : mjH Z ((i : ℕ) + 1) = HLat.ofCoord ((s0Of R F).M i) ((s0Of R F).XW i) :=
  latSeq_succ _ _ _ i

theorem mjH_off {j : ℕ} (h : j = 0 ∨ D.R.m < j) : mjH Z j = unitLat D.what₂.LL (Module.finrank ℂ (D.what₂.Mj j)) :=
  latSeq_off _ _ _ h

def mjCoord (i : Fin D.R.m) : (Fin ((s0Of R F).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (mjH Z ((i : ℕ) + 1)).V :=
  castV (mjH_succ Z i).symm

theorem mjH_good (hH : Holds R F) (j : ℕ) : (mjH Z j).Good :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW (fun _ A _ => A.Good)
    (fun i => ofCoord_good (hH.prim.mLat i) fun v => frame_gram_unit _ (RealDat3.kForm_of (F := F) hH.prim.unif false i v).1)
    (fun _ => unitLat_good _) j

theorem jM_basis (hH : Holds R F) (j : ℕ) : LinearIndependent ℂ (fun k => jM Z j ((mjH Z j).b k)) ∧
    Submodule.span ℂ (Set.range fun k => jM Z j ((mjH Z j).b k)) = ⊤ :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW
    (fun _ A g => LinearIndependent ℂ (fun k => g (A.b k)) ∧ Submodule.span ℂ (Set.range fun k => g (A.b k)) = ⊤)
    (fun i => by
      have h : (fun k => Z.jW i ((HLat.ofCoord ((s0Of R F).M i) ((s0Of R F).XW i)).b k)) = fun k => Z.jW i (Pi.single k 1) :=
        funext fun k => congrArg (Z.jW i) (Pi.basisFun_apply _ _ k)
      exact h ▸ jW_basis Z hH i)
    (fun _ => unitMap_basis _ _) j

theorem jM_lat (hP : Pins R F cG) (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (mjH Z j).V) :
    x ∈ (mjH Z j).L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
      jM Z j x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW
    (fun j A g => ∀ x : A.V, x ∈ A.L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
      g x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v)
    (fun i => (jW_lat Z hP hH i).2) j h1 h2 x

theorem mjLat_sub (hP : Pins R F cG) (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range (jM Z j) :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW (fun j _ g => ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range g)
    (fun i => (jW_lat Z hP hH i).1) j h1 h2

theorem jM_metric (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (mjH Z j).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (mjH Z j).b (mjH Z j).X (InfinitePlace.mk D.what₂.embLL) x) = ‖jM Z j x‖ :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW
    (fun _ A g => ∀ x : A.V, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord A.b A.X (InfinitePlace.mk D.what₂.embLL) x) = ‖g x‖)
    (fun i => jW_norm Z hH i) j h1 h2 x

def mjIds (Xd : DivX D) (h : Xd.MjH = mjH Z) : MjHIds D A3.A Xd (A3.indefDown (s0Of R F)) where
  eW i := castV ((mjH_succ Z i).symm.trans (congrFun h _).symm)

theorem mjHTie_of_eq (Xd : DivX D) (h : Xd.MjH = mjH Z) (hj : HEq Xd.jM (jM Z)) :
    MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW (mjIds Z Xd h) where
  j_eq i x := map_castV _ _ D.what₂.Mj Z.jW h hj i _ x
  hlat i := hLatTie_castV ((mjH_succ Z i).symm.trans (congrFun h _).symm)

theorem exists_mjHTie (Xd : DivX D) (h : Xd.MjH = mjH Z) (hj : HEq Xd.jM (jM Z)) :
    ∃ JM, MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM :=
  ⟨_, mjHTie_of_eq Z Xd h hj⟩

def withMj (hP : Pins R F cG) (hH : Holds R F) (Xd : DivX D)
    (iM : ∀ j c, (mjH Z j).V →ₗ[D.what₂.LL] Xd.geo.Fn (Xd.Yv j c))
    (hiM : ∀ j c x, iM j c x ∈ Xd.geo.H0 (Xd.Yv j c) (Xd.Lw j c (DV.kapW D j))) : DivX D :=
  { Xd with
    MjH := mjH Z
    MjH_good := mjH_good Z hH
    jM := jM Z
    jM_basis := jM_basis Z hH
    jM_lat := jM_lat Z hP hH
    MjLat_sub := mjLat_sub Z hP hH
    jM_metric := jM_metric Z hH
    iMj := iM
    iMj_mem := hiM }

theorem mjHTie_withMj (hP : Pins R F cG) (hH : Holds R F) (Xd : DivX D)
    (iM : ∀ j c, (mjH Z j).V →ₗ[D.what₂.LL] Xd.geo.Fn (Xd.Yv j c))
    (hiM : ∀ j c x, iM j c x ∈ Xd.geo.H0 (Xd.Yv j c) (Xd.Lw j c (DV.kapW D j))) :
    MjHTie D A3.A (withMj Z hP hH Xd iM hiM) (A3.indefDown (s0Of R F)) Z.jW (mjIds Z _ rfl) :=
  mjHTie_of_eq Z _ rfl HEq.rfl

section Reface

variable {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {kap : ℝ} {lam : type_of% R.lam3} {err : type_of% (R.updS kap lam).err0}
  {Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0}
  (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y')

end Reface

example : Module.finrank ℚ (unitLat ℚ 1).V = 1 := Module.finrank_fin_fun ℚ

example : Subsingleton (unitLat ℚ 0).V := inferInstanceAs (Subsingleton (Fin 0 → ℚ))

example (M : Submodule (𝓞 ℚ) (Fin 3 → ℚ)) : Module.finrank ℚ
    (latSeq (m := 1) (d := fun _ => 3) (fun _ => M) (fun _ _ => 1) (fun _ => ℂ) 1).V = 3 := Module.finrank_fin_fun ℚ

end GlobalTheory.Mem.R3

end
