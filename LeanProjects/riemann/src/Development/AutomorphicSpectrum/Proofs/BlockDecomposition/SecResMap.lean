import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapMulE

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change ((φ.hom.app (op U) ≫ G.obj.map g.op).hom x) = ((F.obj.map g.op ≫ φ.hom.app (op V)).hom x)
  rw [φ.hom.naturality]

theorem res_kap (hKS : KapSpec) {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : LocallyConstant U (ZMod q)) {V : Scheme.{0}} (k : V ⟶ U) (a : ZMod q) (h : ∀ v : V, f (k v) = a) :
    Sec.res k (Sec.map (resι _ (tw q i)) (kap i ζ f)) =
      (ULift.up a : ULift.{1} (ZMod q)) • resGen i (primRes k ζ) := by
  obtain ⟨h1, -, -⟩ := hKS q i U ζ f
  unfold CrystallineSemistableComparison.E.IsLC at h1
  rw [sec_res_map, h1 V k a h]
  simp only [GlobalTheory.EtC.Sec.map, GlobalTheory.EtC.resGen, map_smul]

theorem kapMul_of : LcCover → RepRoot → KapSpec → KapMul := by
  intro hLC _ hKS hIn
  unfold CrystallineSemistableComparison.E.InTw at hIn
  intro q _ i j U ζ f g
  have hP := hIn q i j
  let fg : LocallyConstant U (ZMod q × ZMod q) :=
    ⟨fun x => (f x, g x), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  obtain ⟨W, jj, hc, -, -, hglue⟩ := hLC U (ZMod q × ZMod q) fg
  have hpt : ∀ (a : ZMod q × ZMod q) (v : W a), f (jj a v) = a.1 ∧ g (jj a v) = a.2 := by
    intro a v
    have := hc a v
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨y, -, hy⟩ := hglue (ZMod q) ((res (ZMod q) (tw q (i + j))).X 0)
    (fun a => Sec.res (jj a) (Sec.map (resι (ZMod q) (tw q (i + j))) ((kap (i + j) ζ) (f * g))))
  refine (hy _ fun a => ?_).trans (hy _ fun a => rfl).symm
  rw [(twPair q i j).nat]
  rw [res_kap hKS i ζ f (jj a) a.1 fun v => (hpt a v).1,
    res_kap hKS j ζ g (jj a) a.2 fun v => (hpt a v).2,
    res_kap hKS (i + j) ζ (f * g) (jj a) (a.1 * a.2) fun v => by
      rw [LocallyConstant.mul_apply, (hpt a v).1, (hpt a v).2]]
  rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, hP (W a) (primRes (jj a) ζ), smul_smul, mul_comm]
  rfl

end GlobalTheory.CompanionTheory.KapMulE
