import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section CechLoc

variable {R : Type} [CommRing R] {A : Type} [CommRing A]

def clAct {D : Type u} [Category.{v} D] (H : D ⥤ ModuleCat.{w} R) (ρ : ∀ X, A →+* Module.End R (H.obj X)) (p : ℕ) :
    A →+* Module.End R (Cn H p) where
  toFun a := LinearMap.pi fun s => (ρ _ a) ∘ₗ LinearMap.proj s
  map_one' := LinearMap.ext fun f => funext fun s => by simp
  map_mul' a b := LinearMap.ext fun f => funext fun s => by simp [Module.End.mul_apply]
  map_zero' := LinearMap.ext fun f => funext fun s => by simp
  map_add' a b := LinearMap.ext fun f => funext fun s => by simp

theorem clAct_apply {D : Type u} [Category.{v} D] (H : D ⥤ ModuleCat.{w} R) (ρ : ∀ X, A →+* Module.End R (H.obj X))
    (p : ℕ) (a : A) (f : Cn H p) (s : ComposableArrows D p) : clAct H ρ p a f s = ρ _ a (f s) := rfl

theorem clAct_d {D : Type u} [Category.{v} D] (H : D ⥤ ModuleCat.{w} R) (ρ : ∀ X, A →+* Module.End R (H.obj X))
    (hρ : ∀ {X Y : D} (h : X ⟶ Y) a x, (H.map h).hom (ρ X a x) = ρ Y a ((H.map h).hom x)) (p : ℕ) (a : A) (f : Cn H p) :
    d H p (clAct H ρ p a f) = clAct H ρ (p + 1) a (d H p f) := by
  funext s
  change ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (H.map (GlobalTheory.CatH.toLast i s)).hom (ρ _ a (f (GlobalTheory.CatH.face i s))) =
    ρ _ a (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (H.map (GlobalTheory.CatH.toLast i s)).hom (f (GlobalTheory.CatH.face i s)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hρ]

theorem cl_mem_of_pow {X : Type w} [AddCommGroup X] [Module R X] (act : A →+* Module.End R X) (V : Submodule R X)
    (hV : ∀ a, ∀ v ∈ V, act a v ∈ V) {m : ℕ} (f : Fin m → A) (hf : Ideal.span (Set.range f) = ⊤) (z : X)
    (h : ∀ k, ∃ n : ℕ, act (f k ^ n) z ∈ V) : z ∈ V := by
  choose n hn using h
  let I : Ideal A :=
    { carrier := {a | act a z ∈ V}
      add_mem' := fun {a b} ha hb => by
        change act (a + b) z ∈ V
        rw [map_add, LinearMap.add_apply]; exact V.add_mem ha hb
      zero_mem' := by
        change act 0 z ∈ V
        rw [map_zero, LinearMap.zero_apply]; exact V.zero_mem
      smul_mem' := fun c a ha => by
        change act (c * a) z ∈ V
        rw [map_mul, Module.End.mul_apply]; exact hV _ _ ha }
  have hI : Ideal.span ((fun a => a ^ (∑ k, n k)) '' Set.range f) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have e : f k ^ (∑ k, n k) = f k ^ (∑ k, n k - n k) * f k ^ n k := by
      rw [← pow_add, Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))]
    change act (f k ^ (∑ k, n k)) z ∈ V
    rw [e, map_mul, Module.End.mul_apply]
    exact hV _ _ (hn k)
  rw [Ideal.span_pow_eq_top _ hf] at hI
  have h1 : (1 : A) ∈ I := hI Submodule.mem_top
  have h2 : act 1 z ∈ V := h1
  simpa using h2

theorem cl_unif {ι : Type*} [Finite ι] (P : ι → ℕ → Prop) (hP : ∀ i a b, a ≤ b → P i a → P i b)
    (h : ∀ i, ∃ n, P i n) : ∃ N, ∀ i, P i N := by
  cases nonempty_fintype ι
  choose n hn using h
  exact ⟨∑ i, n i, fun i => hP i _ _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (hn i)⟩

instance cl_finite {m p : ℕ} : Finite (ComposableArrows {S : Finset (Fin m) // S.Nonempty} p) :=
  Finite.of_injective (fun s : ComposableArrows {S : Finset (Fin m) // S.Nonempty} p => s.obj)
    (fun s t (h : s.obj = t.obj) => CategoryTheory.Functor.ext (fun x => congrFun h x)
    (fun _ _ _ => Subsingleton.elim _ _))

theorem cl_bij {X : Type w} [AddCommGroup X] [Module R X] (ρS : A →+* Module.End R X) {m : ℕ} (f : Fin m → A)
    (T : Finset (Fin m)) (h : ∀ k ∈ T, Function.Bijective (ρS (f k))) (n : ℕ) :
    Function.Bijective (ρS ((∏ k ∈ T, f k) ^ n)) := by
  have hm : ∀ a b, Function.Bijective (ρS a) → Function.Bijective (ρS b) → Function.Bijective (ρS (a * b)) := by
    intro a b ha hb
    have e : ⇑(ρS (a * b)) = ρS a ∘ ρS b := by
      funext x; rw [map_mul, Module.End.mul_apply]; rfl
    rw [e]; exact ha.comp hb
  have h1 : Function.Bijective (ρS 1) := by rw [map_one]; exact Function.bijective_id
  have hp : Function.Bijective (ρS (∏ k ∈ T, f k)) := by
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty]; exact h1
    | insert a T ha ih =>
      rw [Finset.prod_insert ha]
      exact hm _ _ (h a (Finset.mem_insert_self _ _)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
  induction n with
  | zero => rw [pow_zero]; exact h1
  | succ n ih => rw [pow_succ]; exact hm _ _ ih hp

theorem cl_dvd {m : ℕ} (f : Fin m → A) (k : Fin m) (S : Finset (Fin m)) :
    ∃ c, f k * ∏ j ∈ S, f j = c * ∏ j ∈ insert k S, f j := by
  by_cases hk : k ∈ S
  · rw [Finset.insert_eq_of_mem hk]; exact ⟨f k, rfl⟩
  · rw [Finset.prod_insert hk]; exact ⟨1, (one_mul _).symm⟩

end CechLoc

end CrystallineSemistableComparison.B

namespace CrystallineSemistableComparison.B

section CechLoc2

variable {R : Type} [CommRing R] {A : Type} [CommRing A]

theorem cl_mm {X : Type w} [AddCommGroup X] [Module R X] (ρS : A →+* Module.End R X) (a b : A) (x : X) :
    ρS a (ρS b x) = ρS (a * b) x := by rw [map_mul, Module.End.mul_apply]

abbrev NE (m : ℕ) := {S : Finset (Fin m) // S.Nonempty}

abbrev Kin (m : ℕ) (k : Fin m) := {S : Finset (Fin m) // k ∈ S}

def ins {m : ℕ} (k : Fin m) (S : NE m) : NE m := ⟨insert k S.1, Finset.insert_nonempty _ _⟩

def sng {m : ℕ} (k : Fin m) : NE m := ⟨{k}, Finset.singleton_nonempty k⟩

def leIns {m : ℕ} (k : Fin m) (S : NE m) : S ⟶ ins k S := homOfLE (Finset.subset_insert k S.1)

def sngLe {m : ℕ} (k : Fin m) (S : NE m) : sng k ⟶ ins k S :=
  homOfLE (Finset.singleton_subset_iff.2 (Finset.mem_insert_self k S.1))

theorem cl_gc {m : ℕ} (k : Fin m) :
    GaloisConnection (fun S : NE m => (⟨insert k S.1, Finset.mem_insert_self _ _⟩ : Kin m k))
      (fun T : Kin m k => (⟨T.1, ⟨k, T.2⟩⟩ : NE m)) := fun S T => by
  show insert k S.1 ⊆ T.1 ↔ S.1 ⊆ T.1
  rw [Finset.insert_subset_iff]
  exact and_iff_right T.2

def clL {m : ℕ} (k : Fin m) : NE m ⥤ Kin m k := (cl_gc k).monotone_l.functor

def clU {m : ℕ} (k : Fin m) : Kin m k ⥤ NE m := (cl_gc k).monotone_u.functor

def clInit {m : ℕ} (k : Fin m) : Limits.IsInitial (⟨{k}, Finset.mem_singleton_self k⟩ : Kin m k) :=
  Limits.IsInitial.ofUniqueHom (fun T => homOfLE (Finset.singleton_subset_iff.2 T.2)) (fun _ _ => Subsingleton.elim _ _)

variable {m : ℕ} (G : NE m ⥤ ModuleCat.{w} R)

theorem cl_res (k : Fin m) :
    (cx (clL k ⋙ clU k ⋙ G)).ResUpTo 1 ((Mor.restrict (clU k ⋙ G) (clL k)).hom.f 0 ∘ₗ
      aug (clU k ⋙ G) fun T => ((clU k ⋙ G).map ((clInit k).to T)).hom) := by
  have hi := CrystallineSemistableComparison.P.initial (clU k ⋙ G) _ (clInit k)
  have hb : ∀ n, UpTo (1 : R) ((Mor.restrict (clU k ⋙ G) (clL k)).hom.mapH n) := fun n =>
    (CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict (clU k ⋙ G) (clL k)).hom.mapH n) LinearMap.id 1 1).2.2.2.2.mpr
      (CrystallineSemistableComparison.P.adj (clU k ⋙ G) (clL k) (clU k) (cl_gc k).adjunction n)
  have := (CrystallineSemistableComparison.P.res_transfer (Mor.restrict (clU k ⋙ G) (clL k)).hom _ 1 1 hb).1 hi
  rwa [mul_one] at this

def clNat (k : Fin m) : G ⟶ clL k ⋙ clU k ⋙ G where
  app S := G.map (leIns k S)
  naturality S S' h := by
    simp only [Functor.comp_map]
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg G.map (Subsingleton.elim _ _)

def clα (k : Fin m) (p : ℕ) : Cn G p →ₗ[R] Cn (clL k ⋙ clU k ⋙ G) p := (Mor.ofNatTrans (clNat G k)).hom.f p

theorem clα_apply (k : Fin m) (p : ℕ) (z : Cn G p) (s : ComposableArrows (NE m) p) :
    clα G k p z s = (G.map (leIns k _)).hom (z s) := rfl

theorem clα_d (k : Fin m) (p : ℕ) (z : Cn G p) :
    d (clL k ⋙ clU k ⋙ G) p (clα G k p z) = clα G k (p + 1) (d G p z) :=
  (Mor.ofNatTrans (clNat G k)).d_pullC p z

structure ClD (M : Type w') [AddCommGroup M] [Module R M] (A : Type) [CommRing A] where
  ε : ∀ S, M →ₗ[R] G.obj S
  hε : ∀ S S' (h : S ⟶ S') x, (G.map h).hom (ε S x) = ε S' x
  f : Fin m → A
  span : Ideal.span (Set.range f) = ⊤
  ρ₀ : A →+* Module.End R M
  ρ : ∀ S, A →+* Module.End R (G.obj S)
  hρ : ∀ {S S' : NE m} (h : S ⟶ S') a x, (G.map h).hom (ρ S a x) = ρ S' a ((G.map h).hom x)
  ερ : ∀ S a x, ε S (ρ₀ a x) = ρ S a (ε S x)
  unit : ∀ S : NE m, ∀ k ∈ S.1, Function.Bijective (ρ S (f k))
  surj : ∀ (S : NE m) y, ∃ (n : ℕ) (x : M), ρ S ((∏ k ∈ S.1, f k) ^ n) y = ε S x
  ker : ∀ (S : NE m) x, ε S x = 0 → ∃ n : ℕ, ρ₀ ((∏ k ∈ S.1, f k) ^ n) x = 0

variable {G} {M : Type w'} [AddCommGroup M] [Module R M]

namespace ClD

variable (D : ClD G M A)

theorem e1 (k : Fin m) (S : NE m) (y : G.obj (ins k S)) :
    ∃ (n : ℕ) (x : G.obj S), D.ρ (ins k S) (D.f k ^ n) y = (G.map (leIns k S)).hom x := by
  obtain ⟨n, x0, hx0⟩ := D.surj (ins k S) y
  have hx0' : D.ρ (ins k S) ((∏ j ∈ insert k S.1, D.f j) ^ n) y = D.ε (ins k S) x0 := hx0
  obtain ⟨c, hc⟩ := cl_dvd D.f k S.1
  have bS := cl_bij (D.ρ S) D.f S.1 (D.unit S) n
  have bI := cl_bij (D.ρ (ins k S)) D.f S.1 (fun j hj => D.unit (ins k S) j (Finset.mem_insert_of_mem hj)) n
  obtain ⟨x', hx'⟩ := bS.2 (D.ε S (D.ρ₀ (c ^ n) x0))
  refine ⟨n, x', bI.1 ?_⟩
  rw [← D.hρ, hx', D.hε, D.ερ, ← hx0', cl_mm, cl_mm, ← mul_pow, ← mul_pow, mul_comm _ (D.f k), hc]

theorem e2 (k : Fin m) (S : NE m) (x : G.obj S) (hx : (G.map (leIns k S)).hom x = 0) :
    ∃ N : ℕ, D.ρ S (D.f k ^ N) x = 0 := by
  obtain ⟨n, x0, hx0⟩ := D.surj S x
  have h1 : D.ε (ins k S) x0 = 0 := by
    rw [← D.hε S (ins k S) (leIns k S), ← hx0, D.hρ, hx, map_zero]
  obtain ⟨N, hN⟩ := D.ker _ x0 h1
  have hN' : D.ρ₀ ((∏ j ∈ insert k S.1, D.f j) ^ N) x0 = 0 := hN
  obtain ⟨c, hc⟩ := cl_dvd D.f k S.1
  have bS := cl_bij (D.ρ S) D.f S.1 (D.unit S) (N + n)
  refine ⟨N, bS.1 ?_⟩
  have e : (∏ j ∈ S.1, D.f j) ^ (N + n) * D.f k ^ N =
      c ^ N * (∏ j ∈ insert k S.1, D.f j) ^ N * (∏ j ∈ S.1, D.f j) ^ n := by
    rw [← mul_pow, ← hc]; ring
  rw [map_zero, cl_mm, e, ← cl_mm, hx0, ← cl_mm, ← D.ερ, hN', map_zero, map_zero]

theorem aug_act (a : A) (x : M) : clAct G D.ρ 0 a (aug G D.ε x) = aug G D.ε (D.ρ₀ a x) :=
  funext fun _ => (D.ερ _ a x).symm

end ClD

end CechLoc2

end CrystallineSemistableComparison.B

namespace CrystallineSemistableComparison.B

namespace ClD

variable {R : Type} [CommRing R] {A : Type} [CommRing A] {m : ℕ} {G : NE m ⥤ ModuleCat.{w} R}
  {M : Type w'} [AddCommGroup M] [Module R M] (D : ClD G M A)

theorem act_α (k : Fin m) (p : ℕ) (a : A) (z : Cn G p) :
    clα G k p (clAct G D.ρ p a z) = clAct (clL k ⋙ clU k ⋙ G) (fun S => D.ρ (ins k S)) p a (clα G k p z) :=
  funext fun _ => D.hρ _ a _

theorem hρL (k : Fin m) {X Y : NE m} (h : X ⟶ Y) (a : A) (x : (clL k ⋙ clU k ⋙ G).obj X) :
    ((clL k ⋙ clU k ⋙ G).map h).hom (D.ρ (ins k X) a x) = D.ρ (ins k Y) a (((clL k ⋙ clU k ⋙ G).map h).hom x) :=
  D.hρ _ a x

theorem hi (p : ℕ) (z : Cn G (p + 1)) (hz : d G (p + 1) z = 0) (k : Fin m) :
    ∃ n : ℕ, clAct G D.ρ (p + 1) (D.f k ^ n) z ∈ LinearMap.range (d G p) := by
  have hL := cl_res G k
  obtain ⟨y, hy⟩ := hL.2.2.2 p (clα G k (p + 1) z) (by rw [clα_d, hz, map_zero])
  rw [one_smul] at hy
  obtain ⟨N1, hN1⟩ := cl_unif (fun (s : ComposableArrows (NE m) p) n =>
      ∃ x, D.ρ (ins k _) (D.f k ^ n) (y s) = (G.map (leIns k (s.obj (Fin.last p)))).hom x)
    (fun s a b hab ⟨x, hx⟩ => ⟨D.ρ _ (D.f k ^ (b - a)) x, by
      rw [D.hρ, ← hx, cl_mm, ← pow_add, Nat.sub_add_cancel hab]⟩)
    (fun s => D.e1 k _ (y s))
  choose y'' hy'' using hN1
  have hyy : clAct (clL k ⋙ clU k ⋙ G) (fun S => D.ρ (ins k S)) p (D.f k ^ N1) y = clα G k p y'' := funext hy''
  have hw : ∀ s, (G.map (leIns k _)).hom ((clAct G D.ρ (p + 1) (D.f k ^ N1) z - d G p y'') s) = 0 := by
    intro s
    have : clα G k (p + 1) (clAct G D.ρ (p + 1) (D.f k ^ N1) z - d G p y'') = 0 := by
      rw [map_sub, act_α, ← hy, ← clα_d, ← hyy, clAct_d _ _ (D.hρL k), sub_self]
    exact congrFun this s
  obtain ⟨N2, hN2⟩ := cl_unif (fun (s : ComposableArrows (NE m) (p + 1)) n =>
      D.ρ _ (D.f k ^ n) ((clAct G D.ρ (p + 1) (D.f k ^ N1) z - d G p y'') s) = 0)
    (fun s a b hab hx => by
      rw [← Nat.sub_add_cancel hab, pow_add, ← cl_mm, hx, map_zero])
    (fun s => D.e2 k _ _ (hw s))
  refine ⟨N2 + N1, clAct G D.ρ p (D.f k ^ N2) y'', ?_⟩
  have h3 : clAct G D.ρ (p + 1) (D.f k ^ N2) (clAct G D.ρ (p + 1) (D.f k ^ N1) z - d G p y'') = 0 := funext hN2
  rw [map_sub, sub_eq_zero, ← Module.End.mul_apply, ← map_mul, ← pow_add] at h3
  rw [clAct_d G D.ρ D.hρ, h3]

theorem h0 (z : Cn G 0) (hz : d G 0 z = 0) (k : Fin m) :
    ∃ n : ℕ, clAct G D.ρ 0 (D.f k ^ n) z ∈ LinearMap.range (aug G D.ε) := by
  have hL := cl_res G k
  obtain ⟨y, hy⟩ := hL.2.2.1 (clα G k 0 z) (by rw [clα_d, hz, map_zero])
  rw [one_smul] at hy
  obtain ⟨n, x, hx⟩ := D.surj (sng k) y
  have hx' : D.ρ (sng k) ((∏ j ∈ ({k} : Finset (Fin m)), D.f j) ^ n) y = D.ε (sng k) x := hx
  rw [Finset.prod_singleton] at hx'
  have hw : ∀ s : ComposableArrows (NE m) 0,
      (G.map (leIns k _)).hom ((clAct G D.ρ 0 (D.f k ^ n) z - aug G D.ε x) s) = 0 := by
    intro s
    have h1 : (G.map (leIns k (s.obj (Fin.last 0)))).hom (z s) = (G.map (sngLe k (s.obj (Fin.last 0)))).hom y :=
      (congrFun hy s).symm
    show (G.map (leIns k _)).hom (D.ρ _ (D.f k ^ n) (z s) - D.ε _ x) = 0
    rw [map_sub, D.hρ, h1, ← D.hρ, hx', D.hε, D.hε, sub_self]
  obtain ⟨N2, hN2⟩ := cl_unif (fun (s : ComposableArrows (NE m) 0) N =>
      D.ρ _ (D.f k ^ N) ((clAct G D.ρ 0 (D.f k ^ n) z - aug G D.ε x) s) = 0)
    (fun s a b hab hx => by
      rw [← Nat.sub_add_cancel hab, pow_add, ← cl_mm, hx, map_zero])
    (fun s => D.e2 k _ _ (hw s))
  refine ⟨N2 + n, D.ρ₀ (D.f k ^ N2) x, ?_⟩
  have h3 : clAct G D.ρ 0 (D.f k ^ N2) (clAct G D.ρ 0 (D.f k ^ n) z - aug G D.ε x) = 0 := funext hN2
  rw [map_sub, sub_eq_zero, ← Module.End.mul_apply, ← map_mul, ← pow_add, D.aug_act] at h3
  exact h3.symm

theorem res : (cx G).ResUpTo 1 (aug G D.ε) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun z hz => ?_, fun p z hz => ?_⟩
  · funext s
    change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (G.map (GlobalTheory.CatH.toLast i s)).hom (D.ε _ x) = 0
    rw [Fin.sum_univ_two, D.hε, D.hε]
    simp
  · rw [one_smul]
    refine (Submodule.mem_bot R).1 (cl_mem_of_pow D.ρ₀ ⊥ (fun a v hv => by
      rw [(Submodule.mem_bot R).1 hv, map_zero]; exact Submodule.zero_mem _) D.f D.span x fun k => ?_)
    obtain ⟨n, hn⟩ := D.ker (sng k) x (congrFun hx (ComposableArrows.mk₀ (sng k)))
    have hn' : D.ρ₀ ((∏ j ∈ ({k} : Finset (Fin m)), D.f j) ^ n) x = 0 := hn
    rw [Finset.prod_singleton] at hn'
    exact ⟨n, (Submodule.mem_bot R).2 hn'⟩
  · obtain ⟨x, hx⟩ := cl_mem_of_pow (clAct G D.ρ 0) (LinearMap.range (aug G D.ε))
      (by rintro a _ ⟨x, rfl⟩; exact ⟨D.ρ₀ a x, (D.aug_act a x).symm⟩) D.f D.span z (D.h0 z hz)
    exact ⟨x, by rw [hx, one_smul]⟩
  · obtain ⟨x, hx⟩ := cl_mem_of_pow (clAct G D.ρ (p + 1)) (LinearMap.range (d G p))
      (by rintro a _ ⟨x, rfl⟩; exact ⟨clAct G D.ρ p a x, clAct_d G D.ρ D.hρ p a x⟩) D.f D.span z (D.hi p z hz)
    exact ⟨x, by rw [hx, one_smul]⟩

end ClD

end CrystallineSemistableComparison.B

namespace CrystallineSemistableComparison.B

section CechLoc3

variable {R : Type} [CommRing R] {A : Type} [CommRing A]

def conjR {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {X Y : C} (h : X = Y)
    (ρ : A →+* Module.End R (F.obj Y)) : A →+* Module.End R (F.obj X) := by
  subst h; exact ρ

theorem conjR_apply {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {X Y : C} (h : X = Y)
    (ρ : A →+* Module.End R (F.obj Y)) (a : A) (x : F.obj X) :
    conjR F h ρ a x = (F.map (eqToHom h.symm)).hom (ρ a ((F.map (eqToHom h)).hom x)) := by
  subst h; simp [conjR]

theorem conjR_bij {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {X Y : C} (h : X = Y)
    (ρ : A →+* Module.End R (F.obj Y)) (a : A) (hb : Function.Bijective (ρ a)) :
    Function.Bijective (conjR F h ρ a) := by
  subst h; exact hb

theorem cl_mmF {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : F.obj X) : (F.map g).hom ((F.map f).hom x) = (F.map (f ≫ g)).hom x := by
  rw [F.map_comp]; rfl

end CechLoc3

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.cech_loc : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {m : ℕ} (T' : C) (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S) (Λ : {S : Finset (Fin m) // S.Nonempty} ⥤ C) (e : ∀ S, Λ.obj S = Lc S.1), (∀ S S' (h : S ⟶ S'), lam S.1 ≫ eqToHom (e S).symm ≫ Λ.map h = lam S'.1 ≫ eqToHom (e S').symm) → LocMod F T' Lc lam → (cx (Λ ⋙ F)).ResUpTo 1 (aug (Λ ⋙ F) fun S => (F.map (lam S.1 ≫ eqToHom (e S).symm)).hom) := by
  intro R _ C _ F m T' Lc lam Λ e hc L
  obtain ⟨B, f, hspan, ρ₀, ρ, lam_ρ, tr_ρ, unit, surj, ker⟩ := L
  let D : ClD (Λ ⋙ F) (F.obj T') B :=
    { ε := fun S => (F.map (lam S.1 ≫ eqToHom (e S).symm)).hom
      hε := fun S S' h x => by
        show (F.map (Λ.map h)).hom ((F.map (lam S.1 ≫ eqToHom (e S).symm)).hom x) = _
        rw [cl_mmF, Category.assoc, hc]
        rfl
      f := f
      span := hspan
      ρ₀ := ρ₀
      ρ := fun S => conjR F (e S) (ρ S.1)
      hρ := fun {S S'} h a x => by
        show (F.map (Λ.map h)).hom (conjR F (e S) (ρ S.1) a x) = conjR F (e S') (ρ S'.1) a ((F.map (Λ.map h)).hom x)
        rw [conjR_apply, conjR_apply]
        let t : Lc S.1 ⟶ Lc S'.1 := eqToHom (e S).symm ≫ Λ.map h ≫ eqToHom (e S')
        have ht : lam S.1 ≫ t = lam S'.1 := by
          rw [show lam S.1 ≫ t = (lam S.1 ≫ eqToHom (e S).symm ≫ Λ.map h) ≫ eqToHom (e S') by
            simp [t, Category.assoc], hc]
          simp
        have key := tr_ρ S.1 S'.1 t ht a ((F.map (eqToHom (e S))).hom x)
        have e1 : (F.map (eqToHom (e S'))).hom ((F.map (Λ.map h)).hom x) =
            (F.map t).hom ((F.map (eqToHom (e S))).hom x) := by
          rw [cl_mmF, cl_mmF]
          exact congrArg (fun φ => (F.map φ).hom x) (by simp [t])
        rw [e1, ← key, cl_mmF, cl_mmF]
        exact congrArg (fun φ => (F.map φ).hom _) (by simp [t])
      ερ := fun S a x => by
        show (F.map (lam S.1 ≫ eqToHom (e S).symm)).hom (ρ₀ a x) =
          conjR F (e S) (ρ S.1) a ((F.map (lam S.1 ≫ eqToHom (e S).symm)).hom x)
        rw [conjR_apply, cl_mmF, show (lam S.1 ≫ eqToHom (e S).symm) ≫ eqToHom (e S) = lam S.1 by simp,
          ← lam_ρ, cl_mmF]
      unit := fun S k hk => conjR_bij F (e S) (ρ S.1) (f k) (unit S.1 k hk)
      surj := fun S y => by
        obtain ⟨n, x, hx⟩ := surj S.1 ((F.map (eqToHom (e S))).hom y)
        refine ⟨n, x, ?_⟩
        show conjR F (e S) (ρ S.1) _ y = (F.map (lam S.1 ≫ eqToHom (e S).symm)).hom x
        rw [conjR_apply, hx, cl_mmF]
      ker := fun S x hx => by
        apply ker S.1 x
        have hx' : (F.map (lam S.1 ≫ eqToHom (e S).symm)).hom x = 0 := hx
        rw [show lam S.1 = (lam S.1 ≫ eqToHom (e S).symm) ≫ eqToHom (e S) by simp, ← cl_mmF, hx', map_zero] }
  exact D.res
